import Tusnady.Upper
import Tusnady.Audit.Dependencies
import Lean.Meta.Basic

/-!
Exact statement checks and exhaustive recursive auditing for the upper work.
No missing target theorem is replaced by a goal alias or a conditional theorem.
The component mode can pass with explicitly open goals; complete mode cannot.
-/
open Lean Elab Command

set_option maxRecDepth 10000 in
run_cmd do
  -- These independently written formulas check the proposition definitions,
  -- rather than trusting a target name whose definition might have changed.
  let upperExpected ← liftTermElabM do
    let result ← Term.elabTerm (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      Tusnady.worstDiscrepancy d N ≤ C * Real.rpow (Real.log (2 + (N : ℝ)))
        ((d : ℝ) - (1 / 2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars result
  let coloringExpected ← liftTermElabM do
    let result ← Term.elabTerm (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∀ P : Fin N → Tusnady.Point d,
      Function.Injective P → ∃ χ : Fin N → ℝ, Tusnady.IsSignColoring χ ∧
        ∀ x : Tusnady.Point d, |Tusnady.realAnchoredCount P χ x| ≤
          C * Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1 / 2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars result
  let asymptoticExpected ← liftTermElabM do
    let result ← Term.elabTerm (← `(∀ d : ℕ, 2 ≤ d →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      Tusnady.worstDiscrepancy d N ≤
        C * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars result
  let sharpExpected ← liftTermElabM do
    let result ← Term.elabTerm (← `(∀ d : ℕ, 3 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
        Tusnady.worstDiscrepancy d N ∧
      Tusnady.worstDiscrepancy d N ≤
        C * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)))) (some (mkSort .zero))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars result
  let goals : Array (Name × Name × Expr) := #[
    (`Tusnady.main_upper_bound, ``Tusnady.HigherDimensionalUpperBound, upperExpected),
    (`Tusnady.main_upper_bound_real_colorings, ``Tusnady.ColoringUpperBound, coloringExpected),
    (`Tusnady.main_upper_bound_asymptotic, ``Tusnady.AsymptoticUpperBound, asymptoticExpected),
    (`Tusnady.main_sharp_order, ``Tusnady.SharpHigherDimensionalOrder, sharpExpected)]
  -- Conditional reductions are audited as implications, never as the targets.
  for (_, propName, expected) in goals do
    unless ← liftTermElabM (Meta.isDefEq (mkConst propName) expected) do
      throwError "Target definition {propName} differs from the independently written formula"
    logInfo m!"INDEPENDENT TARGET FORMULA VERIFIED: {propName}"
  let conditionalTargets : Array (Name × Name) := #[
    (``Tusnady.upperBound_of_gaussianFoldMonotonicity, ``Tusnady.HigherDimensionalUpperBound),
    (``Tusnady.coloringUpperBound_of_gaussianFoldMonotonicity, ``Tusnady.ColoringUpperBound),
    (``Tusnady.asymptoticUpperBound_of_gaussianFoldMonotonicity, ``Tusnady.AsymptoticUpperBound),
    (``Tusnady.sharpOrder_of_gaussianFoldMonotonicity, ``Tusnady.SharpHigherDimensionalOrder)]
  for (conditionalName, goalName) in conditionalTargets do
    let info ← getConstInfo conditionalName
    let expected ← liftCoreM <| mkArrow
      (mkConst ``Tusnady.Upper.GaussianFoldMonotonicity) (mkConst goalName)
    unless ← liftTermElabM (Meta.isDefEq info.type expected) do
      throwError "Conditional reduction {conditionalName} does not have exactly the documented analytic premise"
    if ← liftTermElabM (Meta.isDefEq info.type (mkConst goalName)) then
      throwError "Conditional reduction was mistaken for an unconditional goal: {conditionalName}"
    logInfo m!"CONDITIONAL ACTUAL TYPE {conditionalName}: {info.type}"
    logInfo m!"CONDITIONAL PREMISE CHECKED {conditionalName}: GaussianFoldMonotonicity is required; this is NOT the unconditional target"
  let smallConditionalTargets : Array (Name × Name) := #[
    (``Tusnady.upperBound_of_smallGaussianFoldMonotonicity, ``Tusnady.HigherDimensionalUpperBound),
    (``Tusnady.coloringUpperBound_of_smallGaussianFoldMonotonicity, ``Tusnady.ColoringUpperBound),
    (``Tusnady.asymptoticUpperBound_of_smallGaussianFoldMonotonicity, ``Tusnady.AsymptoticUpperBound),
    (``Tusnady.sharpOrder_of_smallGaussianFoldMonotonicity, ``Tusnady.SharpHigherDimensionalOrder)]
  for (conditionalName, goalName) in smallConditionalTargets do
    let info ← getConstInfo conditionalName
    let expected ← liftCoreM <| mkArrow
      (mkConst ``Tusnady.Upper.SmallGaussianFoldMonotonicity) (mkConst goalName)
    unless ← liftTermElabM (Meta.isDefEq info.type expected) do
      throwError "Small-radius reduction {conditionalName} has undocumented hypotheses or a different conclusion"
    if ← liftTermElabM (Meta.isDefEq info.type (mkConst goalName)) then
      throwError "Small-radius reduction was mistaken for an unconditional goal: {conditionalName}"
    logInfo m!"CONDITIONAL ACTUAL TYPE {conditionalName}: {info.type}"
    logInfo m!"CONDITIONAL PREMISE CHECKED {conditionalName}: SmallGaussianFoldMonotonicity is required; this is NOT the unconditional target"
  let env ← getEnv
  let modules := env.header.moduleNames
  let projectConstant := fun (name : Name) =>
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => modules[idx.toNat]!
      | none => env.mainModule
    (`Tusnady).isPrefixOf moduleName || (`Tusnady).isPrefixOf name
  let upperConstant := fun (name : Name) =>
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => modules[idx.toNat]!
      | none => env.mainModule
    (`Tusnady.Upper).isPrefixOf moduleName || (`Tusnady.Upper).isPrefixOf name ||
      goals.any (fun g => g.1 == name)
  let entries := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut projectDependencies : NameSet := {}
  let mut upperCount : Nat := 0
  liftIO <| IO.println "UPPER AUDIT: recursive checks of upper components started"
  for (name, info) in entries do
    if projectConstant name && upperConstant name then
      match info with
      | .thmInfo ti =>
        let closure := TusnadyAudit.collectDependencies env name projectConstant
        unless closure.missing.isEmpty do
          throwError "Missing declarations in component dependency audit: {closure.missing.toList}"
        let axioms ← Lean.collectAxioms name
        let names := String.intercalate ", " (axioms.toList.map Name.toString)
        logInfo m!"AXIOMS {name}: [{names}]"
        for ax in axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unapproved kernel axiom {ax} in {name}"
        if upperConstant name then
          upperCount := upperCount + 1
          if upperCount % 20 == 0 then
            liftIO <| IO.println s!"UPPER AUDIT PROGRESS: {upperCount} component theorems checked"
          logInfo m!"TYPE {name}: {ti.type}"
          let direct := info.getUsedConstantsAsSet.toList.toArray.qsort
            (fun a b => a.toString < b.toString)
          logInfo m!"DIRECT DEPENDENCIES {name}: {direct.toList}"
          let recursive := closure.visited.toList.filter projectConstant
          for dependency in recursive do
            projectDependencies := projectDependencies.insert dependency
          let recursive := recursive.toArray.qsort (fun a b => a.toString < b.toString)
          logInfo m!"RECURSIVE PROJECT DEPENDENCIES {name}: {recursive.toList}"
      | .axiomInfo _ => throwError "Unproved project declaration {name}"
      | _ => pure ()
  logInfo m!"UPPER AUDITED RECURSIVE PROJECT CONSTANTS: {projectDependencies.toList.length}"
  logInfo m!"UPPER AUDITED COMPONENT THEOREMS: {upperCount}"
  let mut complete := true
  for (mainName, propName, expected) in goals do
    logInfo m!"EXPECTED COMPLETE TYPE {mainName}: {expected}"
    match env.find? mainName with
    | some (.thmInfo ti) =>
      logInfo m!"ACTUAL COMPLETE TYPE {mainName}: {ti.type}"
      if ← liftTermElabM (Meta.isDefEq ti.type expected) then
        logInfo m!"UPPER MAIN STATUS {mainName}: EXACT TYPE VERIFIED"
        let closure := TusnadyAudit.collectDependencies env mainName
        unless closure.missing.isEmpty do
          throwError "Incomplete main dependency closure: {closure.missing.toList}"
        let certifiedAxioms ← Lean.collectAxioms mainName
        for ax in certifiedAxioms do
          unless closure.axioms.contains ax do
            throwError "Independent axiom walk omitted {ax} in {mainName}"
        for ax in closure.axioms do
          unless certifiedAxioms.contains ax do
            throwError "Independent axiom walk found unreported {ax} in {mainName}"
        let mainAxioms := String.intercalate ", " (closure.axioms.toList.map Name.toString)
        logInfo m!"AXIOMS {mainName}: [{mainAxioms}]"
        for ax in closure.axioms do
          unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
            throwError "Unapproved kernel axiom {ax} in unconditional main theorem {mainName}"
        let all := closure.visited.toList.toArray.qsort (fun a b => a.toString < b.toString)
        logInfo m!"COMPLETE RECURSIVE DEPENDENCIES {mainName}: {all.toList}"
      else
        complete := false
        logInfo m!"UPPER MAIN STATUS {mainName}: OPEN — actual type differs or has extra hypotheses"
    | some _ =>
      complete := false
      logInfo m!"UPPER MAIN STATUS {mainName}: OPEN — declaration is not a theorem"
    | none =>
      complete := false
      logInfo m!"UPPER MAIN STATUS {mainName}: OPEN — required theorem does not exist"
  if complete then
    logInfo "UPPER COMPLETION STATUS: COMPLETE"
  else
    logInfo "UPPER COMPLETION STATUS: OPEN"

#print Tusnady.upperGrowth
#print Tusnady.HigherDimensionalUpperBound
#print Tusnady.ColoringUpperBound
#print Tusnady.AsymptoticUpperBound
#print Tusnady.SharpHigherDimensionalOrder
#print Tusnady.Anchored
#print Tusnady.trace
#print Tusnady.IsSignColoring
#print Tusnady.coloringDiscrepancy
#print Tusnady.pointDiscrepancy
#print Tusnady.worstDiscrepancy
#print Tusnady.targetGrowth

#print Tusnady.Upper.GaussianFoldMonotonicity
#print Tusnady.upperBound_of_gaussianFoldMonotonicity
#print Tusnady.coloringUpperBound_of_gaussianFoldMonotonicity
#print Tusnady.asymptoticUpperBound_of_gaussianFoldMonotonicity
#print Tusnady.sharpOrder_of_gaussianFoldMonotonicity

#print Tusnady.Upper.SmallGaussianFoldMonotonicity
#print Tusnady.upperBound_of_smallGaussianFoldMonotonicity
#print Tusnady.coloringUpperBound_of_smallGaussianFoldMonotonicity
#print Tusnady.asymptoticUpperBound_of_smallGaussianFoldMonotonicity
#print Tusnady.sharpOrder_of_smallGaussianFoldMonotonicity

#print Tusnady.main_upper_bound
#print Tusnady.main_upper_bound_real_colorings
#print Tusnady.main_upper_bound_asymptotic
#print Tusnady.main_sharp_order
#print Tusnady.main_sharp_order_isTheta
#print Tusnady.Upper.smallRadiusNikolovConstant
#print Tusnady.main_upper_bound_explicit_constant
#print Tusnady.main_upper_bound_real_colorings_explicit_constant
