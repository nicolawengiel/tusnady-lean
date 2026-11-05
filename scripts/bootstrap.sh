#!/bin/sh
# Installs only into this project; no global elan installation is needed.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
mode=install
case "${1:-}" in
  '') ;;
  --offline) mode=offline ;;
  *) echo "Usage: $0 [--offline]" >&2; exit 1 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "Usage: $0 [--offline]" >&2
  exit 1
fi
platform=$(uname -s)
architecture=$(uname -m)
case "$platform/$architecture" in
  Darwin/arm64) target=darwin_aarch64 ;;
  Darwin/x86_64) target=darwin ;;
  Linux/x86_64) target=linux ;;
  Linux/aarch64) target=linux_aarch64 ;;
  *) echo "Unsupported platform: $platform/$architecture" >&2; exit 1 ;;
esac
archive="lean-4.24.0-$target.tar.zst"
if [ "$mode" = offline ]; then
  if [ ! -x "$project_dir/.toolchains/lean-4.24.0-$target/bin/lake" ]; then
    echo "Lokale Toolchain fehlt; die Erstinstallation benötigt Netzwerkzugang." >&2
    exit 1
  fi
  cd "$project_dir"
  ./scripts/lake.sh env lean --version
  python3 scripts/audit_dependencies.py
  python3 scripts/audit_cache_roots.py --installed
  mkdir -p "$project_dir/.cache"
  import_dir=$(mktemp -d "$project_dir/.cache/bootstrap-imports.XXXXXX")
  trap 'rm -f "$import_dir/Imports.lean"; rmdir "$import_dir"' EXIT HUP INT TERM
  python3 - "$project_dir/scripts/cache-roots.txt" "$import_dir/Imports.lean" <<'PY'
from pathlib import Path
import sys
modules = [line.strip() for line in Path(sys.argv[1]).read_text().splitlines()
           if line.strip() and not line.lstrip().startswith("#")]
Path(sys.argv[2]).write_text("".join(f"import {module}\n" for module in modules))
PY
  ./scripts/lake.sh env lean "$import_dir/Imports.lean"
  echo "Offline-Bestandsprüfung erfolgreich: gepinnte Abhängigkeiten und gesamte mathlib-Importkette verfügbar."
  exit 0
fi
mkdir -p "$project_dir/.downloads" "$project_dir/.toolchains"
if [ ! -x "$project_dir/.toolchains/lean-4.24.0-$target/bin/lake" ]; then
  curl -L --fail --retry 3 "https://github.com/leanprover/lean4/releases/download/v4.24.0/$archive" -o "$project_dir/.downloads/$archive"
  if [ -f "$project_dir/scripts/$archive.sha256" ]; then
    (cd "$project_dir/.downloads" && shasum -a 256 -c "$project_dir/scripts/$archive.sha256")
  fi
  tar --zstd -xf "$project_dir/.downloads/$archive" -C "$project_dir/.toolchains"
fi
cd "$project_dir"
if [ ! -f lake-manifest.json ]; then
  MATHLIB_NO_CACHE_ON_UPDATE=1 ./scripts/lake.sh update
else
  ./scripts/lake.sh resolve-deps
fi
set --
while IFS= read -r module || [ -n "$module" ]; do
  case "$module" in ''|'#'*) continue ;; esac
  set -- "$@" "$module"
done < "$project_dir/scripts/cache-roots.txt"
./scripts/lake.sh exe cache get "$@"
