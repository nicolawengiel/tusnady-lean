import Tusnady
import Tusnady.Audit.Dependencies
import Lean.Meta.Basic

/-!
Exhaustive recursive kernel-axiom audit for every project theorem.
The type is printed too: a theorem with an extra hypothesis cannot pass as
an unconditional instance of the target merely because its axiom list is clean.
-/
open Lean Elab Command
open scoped BigOperators
attribute [local instance] Classical.propDecidable

set_option maxRecDepth 10000 in
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let entries := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut count : Nat := 0
  for (name, info) in entries do
    let definingModule := match env.getModuleIdxFor? name with
      | some idx => modules[idx.toNat]!
      | none => env.mainModule
    -- Provenance matters: ported proofs keep their original namespaces.
    if (`Tusnady).isPrefixOf definingModule || (`Tusnady).isPrefixOf name then
      match info with
      | .thmInfo ti =>
        count := count + 1
        if count % 100 == 0 then
          liftIO <| IO.println s!"LOWER AUDIT PROGRESS: {count} component theorems checked"
        logInfo m!"TYPE {name}: {ti.type}"
        let axioms ← Lean.collectAxioms name
        let names := String.intercalate ", " (axioms.toList.map Name.toString)
        logInfo m!"AXIOMS {name}: [{names}]"
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unapproved kernel axiom {ax} in {name}"
      | .axiomInfo _ =>
        throwError "Unproved project constant/axiom declaration {name}"
      | _ => pure ()
  logInfo m!"AUDITED PROJECT THEOREMS: {count}"
  if env.contains `Tusnady.main_lower_bound_unconditional then
    logInfo "UNCONDITIONAL MAIN STATUS: DECLARATION EXISTS; use scripts/check.sh --complete for its exact type"
  else
    logInfo "UNCONDITIONAL MAIN STATUS: OPEN — no theorem Tusnady.main_lower_bound_unconditional exists"


-- Independent formulas detect accidental changes in the target definitions or
-- extra premises in either unconditional lower theorem.
set_option maxRecDepth 10000 in
run_cmd do
  let lowerExpected ← liftTermElabM do
    let result ← Term.elabTerm (← `(∀ d : ℕ, 3 ≤ d →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
        c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
          Tusnady.worstDiscrepancy d N)) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars result
  let coloringExpected ← liftTermElabM do
    let result ← Term.elabTerm (← `(∀ d : ℕ, 3 ≤ d →
      ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∀ N : ℕ, N₀ ≤ N → ∃ P : Fin N → Tusnady.Point d,
          Function.Injective P ∧ (Finset.univ.image P).card = N ∧
          ∀ χ : Fin N → ℝ, Tusnady.IsSignColoring χ → ∃ x : Tusnady.Point d,
            c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
              |∑ i ∈ Tusnady.trace P x, χ i|)) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars result
  unless ← liftTermElabM (Meta.isDefEq (mkConst ``Tusnady.HigherDimensionalLowerBound)
      lowerExpected) do
    throwError "Lower target definition differs from its independently written formula"
  let targets : Array (Name × Expr) := #[
    (``Tusnady.main_lower_bound_unconditional, lowerExpected),
    (``Tusnady.main_lower_bound_real_colorings_unconditional, coloringExpected),
    (``Tusnady.LiteratureProof.sidak, mkConst ``Tusnady.Literature.Sidak),
    (``Tusnady.LiteratureProof.anderson, mkConst ``Tusnady.Literature.Anderson),
    (``Tusnady.LiteratureProof.sampling, mkConst ``Tusnady.Literature.Sampling),
    (``Tusnady.LiteratureProof.conditionalEntropyChainIdentity,
      mkConst ``Tusnady.Literature.ConditionalEntropyChainIdentity),
    (``Tusnady.LiteratureProof.rosenblattUniform, mkConst ``Tusnady.Literature.RosenblattUniform)]
  let env ← getEnv
  for (name, expected) in targets do
    let info ← getConstInfo name
    unless info.isTheorem do
      throwError "Lower completion target {name} is not a theorem"
    unless ← liftTermElabM (Meta.isDefEq info.type expected) do
      throwError "Lower completion target {name} has a different type or additional hypotheses"
    logInfo m!"LOWER EXACT TARGET VERIFIED {name}: {info.type}"
    let closure := TusnadyAudit.collectDependencies env name
    unless closure.missing.isEmpty do
      throwError "Incomplete lower dependency closure: {closure.missing.toList}"
    let certified ← Lean.collectAxioms name
    for ax in certified do
      unless closure.axioms.contains ax do
        throwError "Independent lower axiom walk omitted {ax} in {name}"
    for ax in closure.axioms do
      unless certified.contains ax do
        throwError "Independent lower axiom walk found unreported {ax} in {name}"
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved kernel axiom {ax} in {name}"
    let all := closure.visited.toList.toArray.qsort (fun a b => a.toString < b.toString)
    logInfo m!"COMPLETE RECURSIVE DEPENDENCIES {name}: {all.toList}"
    logInfo m!"LOWER COMPLETE DEPENDENCY COUNT {name}: {all.size}"
    let names := String.intercalate ", " (closure.axioms.toList.map Name.toString)
    logInfo m!"AXIOMS {name}: [{names}]"
  logInfo "LOWER COMPLETION EXACT TARGETS: 7 VERIFIED"

#print Tusnady.HigherDimensionalLowerBound
#print Tusnady.WitnessLowerBound
#print Tusnady.Literature.Assumptions

#print Tusnady.Anchored
#print Tusnady.Box
#print Tusnady.IsSignColoring
#print Tusnady.coloringDiscrepancy
#print Tusnady.pointDiscrepancy
#print Tusnady.worstDiscrepancy
#print Tusnady.targetGrowth
#print Tusnady.Literature.standardGaussian
#print Tusnady.Literature.CenteredGaussian
#print Tusnady.Literature.Sidak
#print Tusnady.Literature.Anderson
#print Tusnady.Literature.Sampling

#print Tusnady.Literature.ConditionalEntropyChainIdentity

#print Tusnady.Literature.RosenblattUniform

#print Tusnady.main_lower_bound
#print Tusnady.main_lower_bound_real_colorings
