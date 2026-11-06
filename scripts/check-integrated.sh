#!/bin/sh
# Mandatory complete audit of the migrated lower/upper proof, Wei and boxes.
# No component-only mode may report the integration target as complete.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_dir"
case "$#:${1:-}" in
  0:) ;;
  1:--standalone) export TUSNADY_PORTABLE_AUDIT=1 ;;
  *) echo "Usage: $0 [--standalone]" >&2; exit 1 ;;
esac
mkdir -p .cache/audit-logs
python3 scripts/verify_upper_baseline.py
python3 scripts/verify_upper_vendor.py
python3 scripts/verify_wei_vendor.py
python3 scripts/audit_dependencies.py
python3 scripts/audit_cache_roots.py --installed
# This includes all preserved lower checks and all four exact upper targets.
if ! ./scripts/check-upper.sh --complete > .cache/audit-logs/integrated-upper-complete.log 2>&1; then
  tail -n 100 .cache/audit-logs/integrated-upper-complete.log
  echo "Migrated lower/upper complete audit failed." >&2
  exit 1
fi
tail -n 6 .cache/audit-logs/integrated-upper-complete.log
./scripts/lake.sh build Wei Tusnady.Boxes Tusnady.Integrated Tusnady.Audit.Dependencies
for audit in WeiAudit BoxesAudit IntegratedAudit; do
  log=".cache/audit-logs/$audit.log"
  if ! ./scripts/lake.sh env lean "$audit.lean" > "$log" 2>&1; then
    tail -n 100 "$log"
    echo "$audit failed: integration is not complete." >&2
    exit 1
  fi
  python3 scripts/audit_axioms.py "$log"
  echo "$audit: complete log at $log"
done
if ! rg -q '^WEI COMPLETION STATUS: COMPLETE$' .cache/audit-logs/WeiAudit.log; then
  echo "Missing Wei exact-type/recursive-axiom completion marker." >&2
  exit 1
fi
if ! rg -q '^BOX COMPLETION STATUS: COMPLETE$' .cache/audit-logs/BoxesAudit.log; then
  echo "Missing box exact-type/recursive-axiom completion marker." >&2
  exit 1
fi
if ! rg -q '^INTEGRATED COMPLETION STATUS: COMPLETE$' .cache/audit-logs/IntegratedAudit.log; then
  echo "Missing integrated exact-type/recursive-axiom completion marker." >&2
  exit 1
fi
python3 scripts/verify_upper_baseline.py
echo "All exact integrated targets and recursive standard-axiom checks passed."
