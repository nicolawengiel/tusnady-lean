#!/usr/bin/env python3
"""Validate #print axioms / audit output against Lean's standard logical axioms."""

from pathlib import Path
import re
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
text = Path(sys.argv[1]).read_text(encoding="utf-8")
groups = re.findall(r"(?:depends on axioms|uses axioms)\s*:?\s*\[([^\]]*)\]", text)
groups += re.findall(r"AXIOMS\s+[^\n]*?:\s*\[([^\]]*)\]", text)
# A theorem with no axioms may be printed as "does not depend on any axioms".
zero_axiom_count = len(re.findall(r"does not depend on any axioms", text))
if not groups and not zero_axiom_count:
    print("Axiomprüfung fehlt: keine maschinenlesbare Axiomliste im Audit.", file=sys.stderr)
    sys.exit(1)
found = set()
for group in groups:
    found.update(name.strip().strip("'\"`") for name in group.split(",") if name.strip())
unexpected = found - ALLOWED
if unexpected:
    print("Nicht zugelassene Axiomabhängigkeiten: " + ", ".join(sorted(unexpected)), file=sys.stderr)
    sys.exit(1)
print(f"Axiomprüfung: {len(groups) + zero_axiom_count} Deklarationen; "
      "nur Lean-Standardaxiome " + ", ".join(sorted(found)) + ".")
