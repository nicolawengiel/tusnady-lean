#!/usr/bin/env python3
"""Reject development holes in project sources, ignoring Lean comments/strings."""

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
EXCLUDED = {".lake", ".toolchains", ".downloads", ".cache"}


def remove_comments_and_strings(source: str) -> str:
    result = list(source)
    i = 0
    depth = 0
    line_comment = False
    string = False
    while i < len(source):
        char = source[i]
        following = source[i:i + 2]
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                result[i] = " "
            i += 1
        elif depth:
            if following == "/-":
                result[i:i + 2] = "  "
                depth += 1
                i += 2
            elif following == "-/":
                result[i:i + 2] = "  "
                depth -= 1
                i += 2
            else:
                if char != "\n":
                    result[i] = " "
                i += 1
        elif string:
            if char == "\\" and i + 1 < len(source):
                result[i:i + 2] = "  "
                i += 2
            elif char == '"':
                result[i] = " "
                string = False
                i += 1
            else:
                if char != "\n":
                    result[i] = " "
                i += 1
        elif following == "--":
            result[i:i + 2] = "  "
            line_comment = True
            i += 2
        elif following == "/-":
            result[i:i + 2] = "  "
            depth = 1
            i += 2
        elif char == '"':
            result[i] = " "
            string = True
            i += 1
        else:
            i += 1
    return "".join(result)


forbidden = re.compile(
    r"\b(?:sorry|admit|axiom|unsafe|proof_wanted|native_decide|"
    r"sorryAx|mkSorry|skipKernelTC|skipKernelTCCheck|ofReduceBool)\b"
)
constant_declaration = re.compile(r"(?m)^[ \t]*(?:(?:private|protected|noncomputable)\s+)*constant\s+[\w.\']+(?=\s|:|\{|\()")
errors = []
files = sorted(path for path in ROOT.rglob("*.lean")
               if not EXCLUDED.intersection(path.relative_to(ROOT).parts))
for path in files:
    source = remove_comments_and_strings(path.read_text(encoding="utf-8"))
    for match in list(forbidden.finditer(source)) + list(constant_declaration.finditer(source)):
        line = source.count("\n", 0, match.start()) + 1
        errors.append(f"{path.relative_to(ROOT)}:{line}: {match.group()}")
if errors:
    print("Offene Beweise, zusätzliche Axiome oder übersprungene Prüfungen:", file=sys.stderr)
    print("\n".join(errors), file=sys.stderr)
    sys.exit(1)
print(f"Quellprüfung: {len(files)} lokale Lean-Dateien ohne verbotene Beweisplatzhalter.")
