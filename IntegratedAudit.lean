import Tusnady.Integrated
import Tusnady.Upper
import Tusnady.Audit.Dependencies
import Lean.Elab.Command
import Lean.Meta.Basic

/-!
Fail-closed integration audit. Expected formulas are written independently
of proposition aliases. Public recursive axiom collection is checked against
a second complete walk through kernel declaration types and values for each
main theorem. All imported project theorems also receive the recursive public
axiom check. This program supplies no premise to any mathematical theorem.
-/
open Lean Elab Command

private def expectedProp (stx : TSyntax `term) : CommandElabM Expr :=
  liftTermElabM do
    let e ← Term.elabTerm stx (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e

private def standardAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Classical.choice || n == ``Quot.sound

private def auditMain (name : Name) (expected : Expr) : CommandElabM Unit := do
  let info ← getConstInfo name
  unless info matches .thmInfo _ do
    throwError "Required main declaration is not a theorem: {name}"
  unless ← liftTermElabM (Meta.isDefEq info.type expected) do
    throwError "Actual type differs from independent target or has extra hypotheses: {name}\nActual: {info.type}\nExpected: {expected}"
  logInfo m!"INTEGRATED EXACT TYPE VERIFIED {name}: {info.type}"
  logInfo m!"INTEGRATED INDEPENDENT EXPECTED TYPE {name}: {expected}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless standardAxiom ax do throwError "Unapproved axiom {ax} in {name}"
  let closure := TusnadyAudit.collectDependencies (← getEnv) name
  unless closure.missing.isEmpty do
    throwError "Incomplete recursive dependency closure for {name}: {closure.missing.toList}"
  for ax in axioms do
    unless closure.axioms.contains ax do
      throwError "Independent walk omitted axiom {ax} in {name}"
  for ax in closure.axioms do
    unless axioms.contains ax do
      throwError "Independent walk found unreported axiom {ax} in {name}"
  logInfo m!"AXIOMS {name}: [{String.intercalate ", " (axioms.toList.map Name.toString)}]"
  let all := closure.visited.toArray.qsort (fun a b => a.toString < b.toString)
  logInfo m!"INTEGRATED COMPLETE RECURSIVE DEPENDENCIES {name}: {all.toList}"
  logInfo m!"INTEGRATED COMPLETE RECURSIVE COUNT {name}: {all.size}"

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
run_cmd do
  let oldLower ← expectedProp (← `(∀ d : ℕ, 3 ≤ d →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
        Tusnady.worstDiscrepancy d N))
  let upper ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Tusnady.worstDiscrepancy d N ≤
      C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1 / 2 : ℝ))))
  let upperColoring ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ P : Fin N → Tusnady.Point d,
      Function.Injective P → ∃ χ : Fin N → ℝ, Tusnady.IsSignColoring χ ∧
        ∀ x : Tusnady.Point d, |Tusnady.realAnchoredCount P χ x| ≤
          C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1 / 2 : ℝ))))
  let planar ← expectedProp (← `(∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
    c * Real.rpow (Real.log (N : ℝ)) ((2 : ℝ) - (1 / 2 : ℝ)) ≤
      Tusnady.worstDiscrepancy 2 N))
  let lower ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
        Tusnady.worstDiscrepancy d N))
  let lowerColoring ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ P : Fin N → Tusnady.Point d, Function.Injective P ∧
        ∀ χ : Fin N → ℝ, Tusnady.IsSignColoring χ → ∃ x : Tusnady.Point d,
          c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
            |Tusnady.realAnchoredCount P χ x|))
  let sharp ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
        Tusnady.worstDiscrepancy d N ∧
      Tusnady.worstDiscrepancy d N ≤
        C * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ))))
  let boxesSharp ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
        Tusnady.Boxes.worstDiscrepancy d N ∧
      Tusnady.Boxes.worstDiscrepancy d N ≤
        C * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ))))
  let combined ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
        Tusnady.worstDiscrepancy d N ∧
      Tusnady.worstDiscrepancy d N ≤ Tusnady.Boxes.worstDiscrepancy d N ∧
      Tusnady.Boxes.worstDiscrepancy d N ≤
        C * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ))))
  let boxUpper ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, Tusnady.Boxes.worstDiscrepancy d N ≤
      C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1 / 2 : ℝ))))
  let boxColoring ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ P : Fin N → Tusnady.Point d,
      Function.Injective P → ∃ χ : Fin N → ℝ, Tusnady.IsSignColoring χ ∧
        ∀ q : Tusnady.Boxes.Query d, |Tusnady.Boxes.realCount P χ q| ≤
          C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1 / 2 : ℝ))))
  let boxCornersColoring ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ P : Fin N → Tusnady.Point d,
      Function.Injective P → ∃ χ : Fin N → ℝ, Tusnady.IsSignColoring χ ∧
        ∀ a b : Tusnady.Point d, |Tusnady.Boxes.realCountCorners P χ a b| ≤
          C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1 / 2 : ℝ))))
  let boxLowerColoring ← expectedProp (← `(∀ d : ℕ, 2 ≤ d →
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∃ P : Fin N → Tusnady.Point d, Function.Injective P ∧
        ∀ χ : Fin N → ℝ, Tusnady.IsSignColoring χ → ∃ a b : Tusnady.Point d,
          (∀ j, a j ≤ b j) ∧
          c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
            |Tusnady.Boxes.realCountCorners P χ a b|))
  let orthantTheta ← expectedProp (← `(∀ {d : ℕ}, 2 ≤ d →
    Asymptotics.IsTheta Filter.atTop (Tusnady.worstDiscrepancy d)
      (fun N : ℕ => Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)))))
  let boxesTheta ← expectedProp (← `(∀ {d : ℕ}, 2 ≤ d →
    Asymptotics.IsTheta Filter.atTop (Tusnady.Boxes.worstDiscrepancy d)
      (fun N : ℕ => Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)))))
  let goals : Array (Name × Expr) := #[
    (``Tusnady.main_lower_bound_unconditional, oldLower),
    (``Tusnady.main_upper_bound, upper),
    (``Tusnady.main_upper_bound_real_colorings, upperColoring),
    (``Tusnady.PlanarWei.planar_lower_bound, planar),
    (``Tusnady.Integrated.lower_bound, lower),
    (``Tusnady.Integrated.lower_bound_real_colorings, lowerColoring),
    (``Tusnady.Integrated.orthant_sharp_order, sharp),
    (``Tusnady.Integrated.boxes_sharp_order, boxesSharp),
    (``Tusnady.Integrated.main_sharp_order, combined),
    (``Tusnady.Boxes.main_upper_bound, boxUpper),
    (``Tusnady.Boxes.main_upper_bound_real_colorings, boxColoring),
    (``Tusnady.Integrated.boxes_upper_bound_real_colorings, boxCornersColoring),
    (``Tusnady.Integrated.boxes_lower_bound_real_colorings, boxLowerColoring),
    (``Tusnady.Integrated.orthant_isTheta, orthantTheta),
    (``Tusnady.Integrated.boxes_isTheta, boxesTheta)]
  for (name, expected) in goals do auditMain name expected
  let env ← getEnv
  let common := TusnadyAudit.collectDependencies env ``Tusnady.Integrated.main_sharp_order
  for required in #[``R56Audit.exists_points, ``Tusnady.main_lower_bound_unconditional,
      ``Tusnady.main_upper_bound] do
    unless common.visited.contains required do
      throwError "Common theorem does not depend on required proved component: {required}"
  if common.visited.contains ``Tusnady.Upper.GaussianFoldMonotonicity then
    throwError "The optional unproved radius-one-fifth fold proposition entered the main chain"
  logInfo "INTEGRATED THREE PROVED COMPONENTS VERIFIED; OPTIONAL FOLD PREMISE ABSENT"
  let modules := env.header.moduleNames
  let isProject := fun (name : Name) =>
    let mod := match env.getModuleIdxFor? name with
      | some idx => modules[idx.toNat]!
      | none => env.mainModule
    (`Tusnady).isPrefixOf mod || (`Wei).isPrefixOf mod
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if isProject name then
      match info with
      | .axiomInfo _ => throwError "Unproved project declaration: {name}"
      | .thmInfo ti =>
        let axs ← Lean.collectAxioms name
        for ax in axs do
          unless standardAxiom ax do throwError "Unapproved axiom {ax} in {name}"
        logInfo m!"AXIOMS {name}: [{String.intercalate ", " (axs.toList.map Name.toString)}]"
        logInfo m!"INTEGRATED COMPONENT TYPE {name}: {ti.type}"
        count := count + 1
      | _ => pure ()
  logInfo m!"INTEGRATED AUDITED PROJECT THEOREMS: {count}"
  logInfo m!"INTEGRATED EXACT MAIN TYPES: {goals.size}"
  logInfo "INTEGRATED COMPLETION STATUS: COMPLETE"

#print R56Audit.exists_points
#print R56Audit.theorem_1_1_unfolded
#print R56Audit.corollary_1_2_lower
#print Tusnady.Point
#print Tusnady.Anchored
#print Tusnady.Box
#print Tusnady.IsSignColoring
#print Tusnady.trace
#print Tusnady.traces
#print Tusnady.pointDiscrepancy
#print Tusnady.worstDiscrepancy
#print Tusnady.targetGrowth
#print Tusnady.Integrated.LowerBound
#print Tusnady.Integrated.SharpOrder
#print Tusnady.Integrated.BoxSharpOrder
#print Tusnady.Integrated.CombinedSharpOrder
#print Tusnady.Integrated.BoxColoringUpperBound
#print Tusnady.Integrated.BoxWitnessLowerBound
#print Tusnady.Boxes.Query
#print Tusnady.Boxes.Query.region
#print Tusnady.Boxes.trace
#print Tusnady.Boxes.realCountCorners
#print Tusnady.Boxes.worstDiscrepancy
#print Tusnady.Integrated.main_sharp_order
#print axioms Tusnady.Integrated.main_sharp_order
#print Tusnady.Integrated.orthant_isTheta
#print axioms Tusnady.Integrated.orthant_isTheta
#print Tusnady.Integrated.boxes_isTheta
#print axioms Tusnady.Integrated.boxes_isTheta
