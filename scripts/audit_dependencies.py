#!/usr/bin/env python3
"""Check that installed source dependencies match the committed lock file."""

import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
EXPECTED_MATHLIB = "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.24.0":
    sys.exit("Unerwartete Lean-Version in lean-toolchain.")
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
packages = manifest["packages"]
mathlib = next(package for package in packages if package["name"] == "mathlib")
if mathlib["rev"] != EXPECTED_MATHLIB:
    sys.exit("Unerwartete mathlib-Revision im Lockfile.")
for package in packages:
    directory = ROOT / manifest["packagesDir"] / package["name"]
    actual = subprocess.check_output(
        ["git", "-C", str(directory), "rev-parse", "HEAD"], text=True
    ).strip()
    if actual != package["rev"]:
        sys.exit(f"Abweichende Revision: {package['name']}: {actual}.")
    dirty = subprocess.check_output(
        ["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"],
        text=True,
    ).strip()
    if dirty:
        sys.exit(f"Lokal veränderte Abhängigkeitsquellen: {package['name']}:\n{dirty}")
print(f"Abhängigkeiten: Lean 4.24.0, mathlib v4.24.0, {len(packages)} unveränderte gepinnte Git-Pakete.")
