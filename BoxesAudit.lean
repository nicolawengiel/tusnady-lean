import Tusnady.Boxes
import Tusnady.Audit.Dependencies
import Lean.Meta.Basic

/-! Exact statements and recursive axiom audit of the new bounded-box bridge.
The sharp target in this component is d ≥ 3; no planar lower input is assumed.
-/
open Lean Elab Command

set_option maxRecDepth 10000 in
run_cmd do
  let upperExpected ← liftTermElabM do
    let e ← Term.elabTerm (← `(∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, Tusnady.Boxes.worstDiscrepancy d N ≤
        C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1/2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let coloringExpected ← liftTermElabM do
    let e ← Term.elabTerm (← `(∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∀ P : Fin N → Tusnady.Point d, Function.Injective P →
        ∃ χ : Fin N → ℝ, Tusnady.IsSignColoring χ ∧
          ∀ q : Tusnady.Boxes.Query d, |Tusnady.Boxes.realCount P χ q| ≤
            C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1/2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let asymptoticExpected ← liftTermElabM do
    let e ← Term.elabTerm (← `(∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        Tusnady.Boxes.worstDiscrepancy d N ≤
          C * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1/2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let sharpExpected ← liftTermElabM do
    let e ← Term.elabTerm (← `(∀ d : ℕ, 3 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1/2 : ℝ)) ≤
          Tusnady.Boxes.worstDiscrepancy d N ∧
        Tusnady.Boxes.worstDiscrepancy d N ≤
          C * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1/2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let targets : Array (Name × Expr) := #[
    (``Tusnady.Boxes.main_upper_bound, upperExpected),
    (``Tusnady.Boxes.main_upper_bound_real_colorings, coloringExpected),
    (``Tusnady.Boxes.main_upper_bound_asymptotic, asymptoticExpected),
    (``Tusnady.Boxes.main_sharp_order, sharpExpected)]
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Tusnady.Boxes).isPrefixOf name then
      match info with
      | .thmInfo ti =>
        count := count + 1
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unproved dependency {ax} in {name}"
        logInfo m!"BOX TYPE {name}: {ti.type}"
        logInfo m!"BOX AXIOMS {name}: [{String.intercalate ", " (axioms.toList.map Name.toString)}]"
      | .axiomInfo _ => throwError "Unproved box axiom {name}"
      | _ => pure ()
  for (name, expected) in targets do
    let info ← getConstInfo name
    unless ← liftTermElabM (Meta.isDefEq info.type expected) do
      throwError "Box target {name} differs from the independently written exact formula"
    let closure := TusnadyAudit.collectDependencies env name
    unless closure.missing.isEmpty do
      throwError "Incomplete box main closure: {closure.missing.toList}"
    let axs ← Lean.collectAxioms name
    for ax in axs do
      unless closure.axioms.contains ax do throwError "Omitted axiom {ax} in {name}"
    for ax in closure.axioms do
      unless axs.contains ax do throwError "Unreported axiom {ax} in {name}"
    logInfo m!"BOX MAIN EXACT TYPE VERIFIED {name}: {expected}"
    logInfo m!"BOX MAIN COMPLETE RECURSIVE DEPENDENCIES {name}: {closure.visited.toList}"
  logInfo m!"BOX AUDITED THEOREMS: {count}; only propext, Classical.choice, Quot.sound"
  logInfo "BOX COMPLETION STATUS: COMPLETE"

#print Tusnady.Boxes.Query
#print Tusnady.Boxes.Query.region
#check @Tusnady.Boxes.Query.region_eq_Icc
#print Tusnady.Boxes.trace
#print Tusnady.Boxes.traces
#print Tusnady.Boxes.pointDiscrepancy
#print Tusnady.Boxes.worstDiscrepancy
#check @Tusnady.Boxes.abs_realCount_le_of_orthants
#check @Tusnady.Boxes.worstDiscrepancy_le_orthant
#check @Tusnady.Boxes.orthant_worstDiscrepancy_le
#check @Tusnady.Boxes.worstDiscrepancy_isTheta_orthant
#check @Tusnady.Boxes.main_sharp_order_isTheta
