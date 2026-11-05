#!/usr/bin/env python3
"""Check direct mathlib import coverage; optionally check installed oleans.

The source scanner also rejects proof holes. Comments and strings are
removed before import discovery, including nested Lean block comments.
"""

from pathlib import Path
import re
import runpy
import sys

ROOT = Path(__file__).resolve().parent.parent
if sys.argv[1:] not in ([], ["--installed"]):
    sys.exit("Aufruf: python3 scripts/audit_cache_roots.py [--installed]")
source_audit = runpy.run_path(str(ROOT / "scripts/audit_sources.py"))
clean = source_audit["remove_comments_and_strings"]
sources = source_audit["files"]
imports = set()
for path in sources:
    source = clean(path.read_text(encoding="utf-8"))
    for line in re.findall(r"(?m)^[ \t]*import[ \t]+[^\n]+", source):
        imports.update(module for module in line.split()[1:] if module.startswith("Mathlib."))
listed = {
    line.strip()
    for line in (ROOT / "scripts/cache-roots.txt").read_text(encoding="utf-8").splitlines()
    if line.strip() and not line.lstrip().startswith("#")
}
missing = sorted(imports - listed)
if missing:
    sys.exit("Cache-Wurzeln fehlen:\n" + "\n".join(missing))
if "--installed" in sys.argv[1:]:
    library = ROOT / ".lake/packages/mathlib/.lake/build/lib/lean"
    absent = sorted(module for module in imports
                    if not (library / (module.replace(".", "/") + ".olean")).is_file())
    if absent:
        sys.exit("Installierte mathlib-Objekte fehlen:\n" + "\n".join(absent))
print(f"Cache-Prüfung: alle {len(imports)} direkten mathlib-Imports aus {len(sources)} "
      f"lokalen Lean-Dateien in {len(listed)} Cache-Wurzeln erfasst."
      + (" Alle direkten .olean-Dateien vorhanden." if "--installed" in sys.argv[1:] else ""))
