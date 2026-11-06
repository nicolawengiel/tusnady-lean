#!/usr/bin/env python3
"""Verify external originals and the completed 4.24 checkpoint are preserved.

Migrated proofs are allowed to change syntax in this integration worktree.
Their mathematical statements are checked separately by Lean's exact-type audit.
"""
from pathlib import Path
import hashlib
import json
import os
import sys

project = Path(__file__).resolve().parents[1]
workspace = project.parent
manifest = json.loads((project / "docs/INTEGRATION_PROTECTED_BASELINE.json").read_text())
failures = []
portable = os.environ.get("TUSNADY_PORTABLE_AUDIT") == "1"
absent = 0
checkpoint = manifest["integration_checkpoint"]
protected = manifest["sha256"] | checkpoint["sha256"]
for relative, expected in protected.items():
    path = workspace / relative
    if not path.is_file():
        if portable and not path.exists() and not path.is_symlink():
            absent += 1
        else:
            failures.append(f"{relative}: fehlt oder ist keine reguläre Datei")
    elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        failures.append(f"{relative}: SHA256 verändert")
# The original mathematical discrepancy definitions need no syntax migration.
# Keep their implementation exact in addition to the independent theorem types.
core = "Tusnady/Definitions.lean"
core_expected = checkpoint["sha256"]["lean-upper/" + core]
if hashlib.sha256((project / core).read_bytes()).hexdigest() != core_expected:
    failures.append(f"{core}: bestehende Diskrepanzdefinitionen verändert")
if failures:
    print("\n".join(failures), file=sys.stderr)
    sys.exit(1)
if absent:
    print(f"Expliziter portabler Prüflauf: {absent} externe Bestandsdateien nicht "
          f"mitgeliefert; {len(protected) - absent} vorhandene externe Dateien "
          "und die lokalen ursprünglichen Diskrepanzdefinitionen unverändert.")
else:
    print(f"Bestandsschutz: {len(manifest['sha256'])} Originaldateien und "
          f"{len(checkpoint['sha256'])} Dateien des abgeschlossenen Checkpoints "
          f"{checkpoint['commit'][:12]} unverändert.")
