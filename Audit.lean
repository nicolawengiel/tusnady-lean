import Tusnady
import Lean.Util.CollectAxioms

/-!
Exhaustive recursive kernel-axiom audit for every project theorem.
The type is printed too: a theorem with an extra hypothesis cannot pass as
an unconditional instance of the target merely because its axiom list is clean.
-/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let entries := env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let mut count := 0
  for (name, info) in entries do
    let definingModule := match env.getModuleIdxFor? name with
      | some idx => modules[idx.toNat]!
      | none => env.mainModule
    -- Provenance matters: ported proofs keep their original namespaces.
    if (`Tusnady).isPrefixOf definingModule || (`Tusnady).isPrefixOf name then
      match info with
      | .thmInfo ti =>
        count := count + 1
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
