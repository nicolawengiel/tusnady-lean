#!/bin/sh
# Default: implemented components. --conditional: the first-stage result.
# --complete: the unconditional target requested in the second stage, fail closed.
set -eu
project_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$project_dir"
mode=components
case "${1:-}" in
  '') ;;
  --conditional) mode=conditional ;;
  --complete) mode=complete ;;
  *) echo "Usage: $0 [--conditional|--complete]" >&2; exit 1 ;;
esac
if [ "$#" -gt 1 ]; then
  echo "Usage: $0 [--conditional|--complete]" >&2
  exit 1
fi
mkdir -p .cache/audit-logs
python3 scripts/audit_dependencies.py
python3 scripts/audit_cache_roots.py --installed
python3 scripts/audit_sources.py
./scripts/lake.sh build
if [ ! -f Audit.lean ]; then
  echo "Audit.lean fehlt: Komponentenprüfung noch nicht vollständig eingerichtet." >&2
  exit 1
fi
# A missing or incorrectly typed main theorem fails immediately in complete mode.
# The full component audit is still mandatory after a successful target check.
if [ "$mode" != components ]; then
  complete_dir=$(mktemp -d "$project_dir/.cache/complete.XXXXXX")
  complete_file="$complete_dir/Complete.lean"
  trap 'rm -f "$complete_file"; rmdir "$complete_dir"' EXIT HUP INT TERM
  if [ "$mode" = conditional ]; then
    cat > "$complete_file" <<'LEAN'
import Tusnady
import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Command
run_cmd do
  let info ← getConstInfo ``Tusnady.main_lower_bound
  let expected ← liftCoreM <| mkArrow (mkConst ``Tusnady.Literature.Assumptions)
    (mkConst ``Tusnady.HigherDimensionalLowerBound)
  unless ← liftTermElabM (Lean.Meta.isDefEq info.type expected) do
    throwError "Actual main declaration type differs from the conditional target"

example : Tusnady.Literature.Assumptions → Tusnady.HigherDimensionalLowerBound :=
  Tusnady.main_lower_bound

#print Tusnady.main_lower_bound
#print axioms Tusnady.main_lower_bound
#print Tusnady.HigherDimensionalLowerBound
#print Tusnady.Literature.Assumptions
LEAN
  else
    cat > "$complete_file" <<'LEAN'
import Tusnady
import Lean.Elab.Command
import Lean.Meta.Basic

open Lean Elab Command
run_cmd do
  let info ← getConstInfo ``Tusnady.main_lower_bound_unconditional
  unless ← liftTermElabM (Lean.Meta.isDefEq info.type
      (mkConst ``Tusnady.HigherDimensionalLowerBound)) do
    throwError "Actual main declaration has extra hypotheses or a different conclusion"

example : Tusnady.HigherDimensionalLowerBound :=
  Tusnady.main_lower_bound_unconditional

#print Tusnady.main_lower_bound_unconditional
#print axioms Tusnady.main_lower_bound_unconditional
#print Tusnady.main_lower_bound_real_colorings_unconditional
#print axioms Tusnady.main_lower_bound_real_colorings_unconditional
#print Tusnady.HigherDimensionalLowerBound
LEAN
  fi
  complete_log=".cache/audit-logs/$mode.log"
  if ! ./scripts/lake.sh env lean "$complete_file" > "$complete_log" 2>&1; then
    cat "$complete_log"
    echo "ZIEL OFFEN ($mode): Der verlangte Hauptsatztyp ist noch nicht nachgewiesen." >&2
    exit 2
  fi
fi
audit_log=.cache/audit-logs/components.log
if ! ./scripts/lake.sh env lean Audit.lean > "$audit_log" 2>&1; then
  cat "$audit_log"
  exit 1
fi
cat "$audit_log"
python3 scripts/audit_axioms.py "$audit_log"
if [ "$mode" = components ]; then
  echo "Komponentenprüfung erfolgreich. Das bestätigt keinen Beweis der Hauptaussage."
  echo "Gesamtziel gesondert prüfen: ./scripts/check.sh --complete"
  exit 0
fi
cat "$complete_log"
python3 scripts/audit_axioms.py "$complete_log"
if [ "$mode" = conditional ]; then
  echo "Bedingtes Ergebnis geprüft: Hauptaussage unter den fünf Literaturvoraussetzungen."
else
  echo "Gesamtziel geprüft: Hauptaussage ohne Literaturvoraussetzungen, nur Lean-Standardaxiome."
fi
