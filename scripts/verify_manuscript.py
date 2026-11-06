#!/usr/bin/env python3
"""Check that every manuscript file present at task start is unchanged."""
from pathlib import Path
import hashlib
import json
import os
import sys

project = Path(__file__).resolve().parents[1]
workspace = project.parent
manifest = json.loads((project / 'docs/manuscript-sha256.json').read_text())
failures = []
portable = os.environ.get("TUSNADY_PORTABLE_AUDIT") == "1"
absent = 0
for relative, expected in manifest.items():
    path = workspace / relative
    if not path.is_file():
        if portable and not path.exists() and not path.is_symlink():
            absent += 1
        else:
            failures.append(f'{relative}: fehlt oder ist keine reguläre Datei')
    elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        failures.append(f'{relative}: SHA256 verändert')
if failures:
    print('\n'.join(failures), file=sys.stderr)
    sys.exit(1)
if absent:
    print(f'Expliziter portabler Prüflauf: {absent} externe Manuskriptdateien '
          f'nicht mitgeliefert; {len(manifest) - absent} vorhandene unverändert.')
else:
    print(f'Manuskriptprüfung: {len(manifest)} ursprüngliche Dateien unverändert.')
