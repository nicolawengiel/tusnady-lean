#!/bin/sh
# The implemented components and the old lower theorem are mandatory.
# --complete additionally requires all four exact unconditional upper targets.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_dir"
mode=components
case "${1:-}" in
  '') ;;
  --complete) mode=complete ;;
  *) echo "Usage: $0 [--complete]" >&2; exit 1 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "Usage: $0 [--complete]" >&2
  exit 1
fi
mkdir -p .cache/audit-logs
# Verify the protected original and the copied lower sources before any build.
python3 scripts/verify_upper_baseline.py
python3 scripts/verify_upper_vendor.py
# Preserve the released lower checks verbatim, including its exact target type.
./scripts/check.sh --complete > .cache/audit-logs/lower-preservation.log 2>&1 || {
  cat .cache/audit-logs/lower-preservation.log
  echo "Die vorhandene Prüfung der unteren Schranke ist fehlgeschlagen." >&2
  exit 1
}
tail -n 4 .cache/audit-logs/lower-preservation.log
./scripts/lake.sh build Tusnady.Upper
audit_log=.cache/audit-logs/upper-components.log
if ! ./scripts/lake.sh env lean UpperAudit.lean > "$audit_log" 2>&1; then
  cat "$audit_log"
  exit 1
fi
python3 scripts/audit_axioms.py "$audit_log"
sed -n '/^UPPER AUDITED /p; /^UPPER MAIN STATUS /p; /^UPPER COMPLETION STATUS:/p' "$audit_log"
if [ "$mode" = components ]; then
  echo "Obere Komponenten geprüft; vollständige Typen und Abhängigkeiten: $audit_log"
  echo "Dies bestätigt keinen noch offenen oberen Hauptsatz. Gesamtprüfung: ./scripts/check-upper.sh --complete"
  exit 0
fi
if ! rg -q '^UPPER COMPLETION STATUS: COMPLETE$' "$audit_log"; then
  echo "ZIEL OFFEN (upper complete): Mindestens einer der vier exakten Hauptsätze fehlt oder hat zusätzliche Hypothesen." >&2
  exit 2
fi
echo "Obere Schranke, eine Färbung für alle Orthanten, Asymptotik und scharfe Größenordnung exakt und rekursiv geprüft."
