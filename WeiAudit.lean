import Wei.R56Audit.Parameters
import Tusnady.Audit.Dependencies
import Lean.Meta.Basic

/-!
# Independent type and full dependency checks for the imported Wei interface

The software proof is MIT copyright (c) 2026 Zhewei Wei; its exact source,
license and import-only adaptations are archived in vendor/wei-6f14d177.
This audit does not replace the independent build of those source files.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000
open MeasureTheory

namespace WeiAuditExpected

def theorem11 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    ENNReal.ofReal (1 - Real.exp (-A * n)) ≤
      (MeasureTheory.Measure.pi fun _ : Fin n =>
        (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict (Set.Icc 0 1))
      {P : Fin n → ℝ × ℝ | ∀ χ : Fin n → ℤˣ,
        ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1,
          c * Real.logb 2 (n : ℝ) ^ (3 / 2 : ℝ) ≤
            |∑ i : Fin n,
              if 0 ≤ (P i).1 ∧ (P i).1 ≤ x ∧ 0 ≤ (P i).2 ∧ (P i).2 ≤ y
              then (((χ i : ℤˣ) : ℤ) : ℝ) else 0|}

def existsPoints : Prop :=
  ∀ {A : ℝ}, 0 < A → ∀ {b : ℕ},
    A + 2 ≤ Real.log ((b : ℝ) / 48) / 2 →
    A + 2 + Real.log 2 ≤ (b : ℝ) / 4096 →
    ∀ {n : ℕ}, 1 ≤ n →
      ∃ P : Fin n → ℝ × ℝ, Function.Injective P ∧
        (∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) ∧
        ∀ χ : Fin n → ℤˣ,
          R56Audit.cA b * Real.logb 2 n ^ (3 / 2 : ℝ) < R56Audit.supNorm χ P

def corollaryLower : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
    c * Real.logb 2 n ^ (3 / 2 : ℝ) < Riesz.PointSets.Δ₂ n

example : theorem11 := R56Audit.theorem_1_1_unfolded
example : existsPoints := R56Audit.exists_points
example : corollaryLower := R56Audit.corollary_1_2_lower

end WeiAuditExpected

#check R56Audit.theorem_1_1_unfolded
#check R56Audit.exists_points
#check R56Audit.corollary_1_2_lower
#print R56Audit.cA
#print R56Audit.F
#print R56Audit.supNorm
#print Riesz.PointSets.Δ₂
#print axioms R56Audit.theorem_1_1_unfolded
#print axioms R56Audit.exists_points
#print axioms R56Audit.corollary_1_2_lower

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array (Name × Name) := #[
    (`R56Audit.theorem_1_1_unfolded, `WeiAuditExpected.theorem11),
    (`R56Audit.exists_points, `WeiAuditExpected.existsPoints),
    (`R56Audit.corollary_1_2_lower, `WeiAuditExpected.corollaryLower)]
  IO.FS.createDirAll ".cache/audit-logs"
  for (root, expected) in targets do
    let info ← getConstInfo root
    unless ← liftTermElabM (Meta.isDefEq info.type (mkConst expected)) do
      throwError "Wei target type differs from the independently stated formula: {root}"
    IO.println s!"EXACT WEI TYPE VERIFIED: {root}"
    let closure := TusnadyAudit.collectDependencies env root
    unless closure.missing.isEmpty do
      throwError "Missing checked kernel constants in Wei audit: {closure.missing.toList}"
    let certifiedAxioms ← Lean.collectAxioms root
    let walkedAxioms := closure.axioms.toArray.qsort Name.lt
    unless certifiedAxioms == walkedAxioms do
      throwError "Public and independent recursive axiom scans disagree: {root}"
    for axiomName in certifiedAxioms do
      unless [`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Additional axiom in Wei proof: {axiomName}"
    let mut modules : NameSet := {}
    for n in closure.visited do
      if (`Oscillation.Direct).isPrefixOf n || (`Oscillation.R56).isPrefixOf n ||
          (`Oscillation.R65).isPrefixOf n || n == `Oscillation.paper_lower_bound ||
          n == `Oscillation.gridPotential then
        throwError "Historical comparison proof reached by primary Wei theorem: {n}"
      if let some i := env.getModuleIdxFor? n then
        let m := env.header.moduleNames[i.toNat]!
        if (`Wei).isPrefixOf m then modules := modules.insert m
    for required in [`R56Audit.proposition_2_7, `R56Audit.roadmap_digits,
        `R56Audit.local_gain, `R56Audit.fact_2_2_general, `R56Audit.fact_A_1,
        `R56Audit.lemma_2_4_digits, `R56Audit.lemma_2_5_ii,
        `R56Audit.lemma_2_6_digits, `R56Audit.condExp_digitSigma] do
      unless closure.visited.contains required do
        throwError "Required primary Wei route theorem absent: {required}"
    let names := closure.visited.toArray.qsort Name.lt
    IO.FS.writeFile s!".cache/audit-logs/{root}.dependencies.txt"
      (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
    IO.println s!"FULL WEI CLOSURE VERIFIED: {root}; {closure.visited.size} constants; {modules.size} Wei modules; axioms {certifiedAxioms}; primary route present; historical comparison absent; no missing constants"
  IO.println "WEI COMPLETION STATUS: COMPLETE"
