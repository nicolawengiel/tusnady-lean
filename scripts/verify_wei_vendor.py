#!/usr/bin/env python3
"""Check the fixed MIT Wei software snapshot, adaptations, pins and options.

Read-only, standard library only. No network access and no manuscript files.
Mathematical validity is checked separately by the actual Lean build/WeiAudit.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
VENDOR = ROOT / "vendor/wei-6f14d177"
COMMIT = "6f14d177668e79a9155f7cd60496313514ad0c9e"
TREE = "d902ca643175d01c890605a55e446153ea76b1bf"
MATHLIB = "d13f23b723b8a846827a245b89c10fc7d3f11612"
TOOLCHAIN = "leanprover/lean4:v4.34.1"
REPOSITORY = "https://github.com/wzskytop/tusnady-lean"


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def digest(data: bytes, algorithm: str = "sha256") -> str:
    return hashlib.new(algorithm, data).hexdigest()


def git_blob(data: bytes) -> str:
    return digest(f"blob {len(data)}\0".encode() + data, "sha1")


def within(path: Path, base: Path) -> bool:
    return path.resolve().is_relative_to(base.resolve())


def option_table(source: str, table: str) -> dict:
    """Read the simple boolean-only option sublanguage, rejecting other values."""
    tables = re.split(r"(?m)^\s*\[([^\[\]\n]+)\]\s*$", source)
    matches = [tables[i + 1] for i in range(1, len(tables), 2) if tables[i].strip() == table]
    require(len(matches) == 1, f"Missing or duplicate option table: {table}")
    options = {}
    for line in matches[0].splitlines():
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        if line.startswith("["):
            break
        entry = re.fullmatch(r"([A-Za-z][A-Za-z0-9_.]*)\s*=\s*(true|false)", line)
        require(entry is not None, f"Unsupported or malformed Lean option: {line}")
        key, value = entry.groups()
        require(key not in options, f"Duplicate Lean option: {key}")
        options[key] = value == "true"
    return options


def wei_library_blocks(source: str) -> list:
    blocks = re.split(r"(?m)^\s*\[\[lean_lib\]\]\s*$", source)[1:]
    answer = []
    for block in blocks:
        block = re.split(r"(?m)^\s*\[\[", block, maxsplit=1)[0]
        name = re.search(r'(?m)^\s*name\s*=\s*"([^"\n]+)"\s*$', block)
        require(name is not None, "Lean library has no unambiguous name")
        if name.group(1) == "Wei":
            answer.append(block)
    return answer


def main() -> None:
    manifest = json.loads((VENDOR / "provenance.json").read_text())
    require(manifest["repository"] == REPOSITORY, "Wei repository differs")
    require(manifest["commit"] == COMMIT, "Wei commit differs")
    require(manifest["git_tree_sha"] == TREE, "Wei tree differs")
    require(manifest["software_license"] == "MIT", "Wei license declaration differs")
    require(manifest["upstream_lean_toolchain"] == TOOLCHAIN, "Wei toolchain differs")
    require(manifest["upstream_mathlib_commit"] == MATHLIB, "Wei mathlib differs")

    tree = json.loads((VENDOR / "source-tree.json").read_text())
    require(tree["sha"] == TREE and tree["truncated"] is False, "Incomplete Wei tree")
    entries = tree["tree"]
    require(len(entries) == 148, "Wei tree entry count differs")
    by_path = {entry["path"]: entry for entry in entries}
    require(len(by_path) == len(entries), "Duplicate Wei tree paths")
    directories = {"": TREE}
    directories.update({e["path"]: e["sha"] for e in entries if e["type"] == "tree"})
    for directory, expected in directories.items():
        prefix = directory + "/" if directory else ""
        children = []
        for entry in entries:
            if not entry["path"].startswith(prefix):
                continue
            name = entry["path"][len(prefix):]
            if "/" in name:
                continue
            is_tree = entry["type"] == "tree"
            mode = entry["mode"].lstrip("0") if is_tree else entry["mode"]
            payload = (mode + " " + name).encode() + b"\0" + bytes.fromhex(entry["sha"])
            children.append(((name + ("/" if is_tree else "")).encode(), payload))
        payload = b"".join(item[1] for item in sorted(children))
        actual = digest(f"tree {len(payload)}\0".encode() + payload, "sha1")
        require(actual == expected, f"Git tree mismatch: {directory or '/'}")

    sources = manifest["sources"]
    require(len(sources) == 125, "Wei software selection count differs")
    originals = {}
    for source in sources:
        path = source["path"]
        require(path in by_path and by_path[path]["type"] == "blob", f"Unknown Wei source {path}")
        stored = VENDOR / source["storage_path"]
        require(within(stored, VENDOR / "original"), f"Escaping original path {path}")
        data = stored.read_bytes()
        require(digest(data) == source["sha256"], f"Original SHA-256 mismatch: {path}")
        require(git_blob(data) == source["git_blob_sha1"] == by_path[path]["sha"],
                f"Original Git blob mismatch: {path}")
        require(len(data) == source["size"], f"Original size mismatch: {path}")
        require(stored.suffix not in {".pdf", ".tex", ".html"}, f"Manuscript extension: {path}")
        require(not path.startswith("verification/"), f"Manuscript artifact: {path}")
        require(Path(path).name != "MANUSCRIPT_LICENSE.md", "Manuscript scope file imported")
        originals[path] = data
    actual_originals = {p.resolve() for p in (VENDOR / "original").rglob("*") if p.is_file()}
    expected_originals = {(VENDOR / s["storage_path"]).resolve() for s in sources}
    require(actual_originals == expected_originals, "Unlisted or missing original software files")
    require(sum(p.endswith(".lean") for p in originals) == 106, "Wei Lean selection differs")
    for p in VENDOR.rglob("*"):
        require(not p.is_file() or p.suffix not in {".pdf", ".tex", ".html"},
                f"Forbidden manuscript file in vendor: {p}")

    license_data = originals["LICENSE"]
    require((VENDOR / "LICENSE").read_bytes() == license_data, "Wei MIT license changed")
    require(b"MIT License" in license_data and b"Copyright (c) 2026 Zhewei Wei" in license_data,
            "Wei MIT attribution absent")

    closure = set(manifest["target_import_closure"])
    require(len(closure) == 83 and "R56Audit.Parameters" in closure, "Wei import closure differs")
    changes = manifest["integration_changes"]
    require(len(changes) == 83, "Wei active source count differs")
    header = """/-
Copyright (c) 2026 Zhewei Wei. Distributed under the MIT license.
See vendor/wei-6f14d177/LICENSE and provenance.json.
Source: wzskytop/tusnady-lean, commit 6f14d177668e79a9155f7cd60496313514ad0c9e.
Integration adaptation: local import module names are prefixed with `Wei`;
mathematical namespaces and proof bodies are unchanged.
-/
"""
    active_modules = set()
    for change in changes:
        active = ROOT / change["path"]
        require(within(active, ROOT / "Wei"), f"Escaping active source {active}")
        data = active.read_bytes()
        require(digest(data) == change["sha256"], f"Active source hash mismatch: {active}")
        text = data.decode()
        require(text.startswith(header), f"Wei attribution header differs: {active}")
        restored = re.sub(r"(^\s*import\s+)Wei\.([\w.]+)", r"\1\2", text[len(header):], flags=re.M)
        require(restored.encode() == originals[change["original_path"]],
                f"Unrecorded Wei proof/namespace change: {active}")
        module = change["original_path"][:-5].replace("/", ".")
        active_modules.add(module)
        for dep in re.findall(r"^\s*import\s+([\w.]+)", text[len(header):], re.M):
            if dep.startswith("Wei."):
                require(dep[4:] in closure, f"Unlisted local import: {dep}")
            else:
                require(dep.startswith("Mathlib."), f"Unexpected external import: {dep}")
    require(active_modules == closure, "Active Wei modules differ from closure")
    wrapper = manifest["active_wrapper"]
    require(digest((ROOT / wrapper["path"]).read_bytes()) == wrapper["sha256"],
            "Wei import wrapper changed")

    libraries = wei_library_blocks((ROOT / "lakefile.toml").read_text())
    require(len(libraries) == 1, "Wei Lake library missing or duplicated")
    active_options = option_table(libraries[0], "lean_lib.leanOptions")
    original_options = option_table(originals["lakefile.toml"].decode(), "leanOptions")
    require(active_options == original_options, "Wei-specific Lean options differ from upstream")
    options_json = json.dumps(active_options, sort_keys=True, separators=(",", ":")).encode()
    require(digest(options_json) == manifest["wei_lean_options_sha256"],
            "Wei-specific options hash differs")
    for artifact in manifest["verification_artifacts"]:
        path = ROOT / artifact["path"]
        require(within(path, ROOT), f"Escaping verification artifact: {path}")
        require(digest(path.read_bytes()) == artifact["sha256"],
                f"Wei bridge/audit artifact hash mismatch: {path}")
    require((ROOT / "lean-toolchain").read_text().strip() == TOOLCHAIN,
            "Project Lean toolchain differs")
    lock = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = [x for x in lock["packages"] if x["name"] == "mathlib"]
    require(len(packages) == 1 and packages[0]["rev"] == MATHLIB, "Project mathlib lock differs")
    print("WEI VENDOR VERIFIED: fixed commit/tree; 10 Merkle trees; 125 software originals; "
          "106 Lean sources; 83 import-only active adaptations; MIT attribution; no manuscripts; "
          "Lean 4.34.1, pinned mathlib and original Wei-specific options")
    print("Mathematical checking remains the separate Lean build and WeiAudit.lean invocation.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, TypeError) as exc:
        print(f"WEI VENDOR CHECK FAILED: {exc}", file=sys.stderr)
        sys.exit(1)
