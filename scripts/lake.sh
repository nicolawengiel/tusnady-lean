#!/bin/sh
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
platform=$(uname -s)
architecture=$(uname -m)
case "$platform/$architecture" in
  Darwin/arm64) target=darwin_aarch64 ;;
  Darwin/x86_64) target=darwin ;;
  Linux/x86_64) target=linux ;;
  Linux/aarch64) target=linux_aarch64 ;;
  *) echo "Unsupported platform: $platform/$architecture" >&2; exit 1 ;;
esac
toolchain_dir="$project_dir/.toolchains/lean-4.24.0-$target"
if [ ! -x "$toolchain_dir/bin/lake" ]; then
  echo "Local Lean toolchain missing. Run ./scripts/bootstrap.sh first." >&2
  exit 1
fi
export PATH="$toolchain_dir/bin:$PATH"
export XDG_CACHE_HOME="$project_dir/.cache"
export MATHLIB_NO_CACHE_ON_UPDATE=1
cd "$project_dir"
exec "$toolchain_dir/bin/lake" "$@"
