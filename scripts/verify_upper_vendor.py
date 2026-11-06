#!/usr/bin/env python3
"""Check the frozen original analytic source files used for the Lean port."""
from pathlib import Path
import hashlib
import json
import sys

project = Path(__file__).resolve().parents[1]
vendor = project / "vendor/openai-math-4eaee875"
data = json.loads((vendor / "provenance.json").read_text())
failures = []
if data["commit"] != "4eaee87548250b2682affda7d05d947c05554bae":
    failures.append("Ursprünglicher analytischer Quell-Commit stimmt nicht.")
if not (vendor / "LICENSE").is_file():
    failures.append("Apache-2.0-Lizenz fehlt.")
for source in data["sources"]:
    path = vendor / source["storage_path"]
    if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != source["sha256"]:
        failures.append(f"Eingefrorene Quelle verändert oder fehlt: {source['path']}")
project_sources = data["ports"] + data.get("derived_modules", []) + data.get("project_native_sources", [])
for source in project_sources:
    path = project / source["path"]
    if not path.is_file():
        failures.append(f"Projektquelle fehlt: {source['path']}")
    elif "sha256" in source and hashlib.sha256(path.read_bytes()).hexdigest() != source["sha256"]:
        failures.append(f"Projektquellen-Provenienz abweichend: {source['path']}")
if failures:
    print("\n".join(failures), file=sys.stderr)
    sys.exit(1)
print(f"Analytische Quellprovenienz: {len(data['sources'])} eingefrorene Originale "
      f"zum Commit {data['commit']} unverändert; {len(project_sources)} Projektquellen "
      f"mit Prüfsummen erfasst; Lizenz vorhanden.")
