import Tusnady.MainUnconditional
import Tusnady.LiteratureEntropyChain
import Lean.Util.CollectAxioms

/-!
Second-stage exact-type and recursive-axiom audit. All five unchanged literature propositions are checked, including their actual
declaration types and recursive standard-axiom dependencies.
-/
example : Tusnady.Literature.Sampling := Tusnady.LiteratureProof.sampling
example : Tusnady.Literature.Sidak := Tusnady.LiteratureProof.sidak
example : Tusnady.Literature.Anderson := Tusnady.LiteratureProof.anderson
example : Tusnady.Literature.RosenblattUniform := Tusnady.LiteratureProof.rosenblattUniform
example : Tusnady.Literature.ConditionalEntropyChainIdentity :=
  Tusnady.LiteratureProof.conditionalEntropyChainIdentity

#print Tusnady.LiteratureProof.sampling
#print axioms Tusnady.LiteratureProof.sampling
#print Tusnady.LiteratureProof.sidak
#print axioms Tusnady.LiteratureProof.sidak
#print Tusnady.LiteratureProof.anderson
#print axioms Tusnady.LiteratureProof.anderson
#print Tusnady.LiteratureProof.rosenblattUniform
#print axioms Tusnady.LiteratureProof.rosenblattUniform

#print Tusnady.LiteratureProof.conditionalEntropyChainIdentity
#print axioms Tusnady.LiteratureProof.conditionalEntropyChainIdentity

open Lean Elab Command
run_cmd do
  for (name, target) in [(``Tusnady.LiteratureProof.sampling, ``Tusnady.Literature.Sampling),
      (``Tusnady.LiteratureProof.sidak, ``Tusnady.Literature.Sidak),
      (``Tusnady.LiteratureProof.anderson, ``Tusnady.Literature.Anderson),
      (``Tusnady.LiteratureProof.rosenblattUniform, ``Tusnady.Literature.RosenblattUniform),
      (``Tusnady.LiteratureProof.conditionalEntropyChainIdentity,
        ``Tusnady.Literature.ConditionalEntropyChainIdentity)] do
    let info ← getConstInfo name
    unless ← liftTermElabM (Lean.Meta.isDefEq info.type (mkConst target)) do
      throwError "Unexpected actual declaration type for {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved kernel axiom {ax} in {name}"
  logInfo "LITERATURE STATUS: ALL FIVE ORIGINAL LITERATURE PROPOSITIONS PROVED; ONLY STANDARD AXIOMS"
