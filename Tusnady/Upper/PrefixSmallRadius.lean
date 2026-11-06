import Tusnady.Upper.PrefixGaussian

/-!
# Prefix signing with a conservative universal radius

This is the same proved backward recursion with radius 1/1000.  Its explicit
monotonicity argument is proved in `Ehrhard.VerticalFoldMonotonicity` and
supplied when this reduction is used in the unconditional upper bound.
The resulting factor 1000 is universal, so it does not change the target rate.
-/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Tusnady.Upper

/-- The concrete small-radius analytic proposition, proved in
`Ehrhard.VerticalFoldMonotonicity`; this definition introduces no axiom. -/
def SmallGaussianFoldMonotonicity : Prop :=
  ∀ k : ℕ, ∀ K : Set (EuclideanSpace ℝ (Fin k)),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) →
    ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ (1 : ℝ)/1000 →
      (1 : ℝ)/2 ≤ (euclideanGaussian k).real K →
      (euclideanGaussian k).real K ≤ (euclideanGaussian k).real (signingFold u K)

/-- The prefix conclusion retains its precise analytic input visibly. -/
theorem prefix_signing_of_smallGaussianFoldMonotonicity
    (hfold : SmallGaussianFoldMonotonicity) {k N : ℕ} (hN : 0 < N)
    (K : Set (EuclideanSpace ℝ (Fin k))) (hKcomp : IsCompact K)
    (hKconv : Convex ℝ K) (hKsymm : ∀ x ∈ K, -x ∈ K)
    (hKmass : 1 - 1/(2*(N : ℝ)) ≤ (euclideanGaussian k).real K)
    (v : Fin N → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ χ : Fin N → Bool, ∀ j (hj : j ≤ N), 0 < j →
      (∑ i : Fin j,
        Tusnady.sign (χ ⟨i.val, lt_of_lt_of_le i.isLt hj⟩) •
          v ⟨i.val, lt_of_lt_of_le i.isLt hj⟩) ∈
        (fun x : EuclideanSpace ℝ (Fin k) => (1000 : ℝ) • x) '' K := by
  let Good : Set (EuclideanSpace ℝ (Fin k)) → Prop :=
    fun A => IsClosed A ∧ Convex ℝ A ∧ ∀ x ∈ A, -x ∈ A
  let Allowed : EuclideanSpace ℝ (Fin k) → Prop := fun u => ‖u‖ ≤ (1 : ℝ)/1000
  have rules : TransformRules (euclideanGaussian k) K Good Allowed signingFold :=
    signingFold_transformRules (euclideanGaussian k) K hKcomp hKconv hKsymm Allowed (hfold k)
  let w : Fin N → EuclideanSpace ℝ (Fin k) := fun i => (1/1000 : ℝ) • v i
  have hw : ∀ i, Allowed (w i) := by
    intro i
    change ‖(1/1000 : ℝ) • v i‖ ≤ (1 : ℝ)/1000
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1/1000), mul_one]
      using mul_le_mul_of_nonneg_left (hv i) (by norm_num : (0 : ℝ) ≤ 1/1000)
  have hn : (N : ℝ) * (1/(2*(N : ℝ))) ≤ (1 : ℝ)/2 := by
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    norm_num
  obtain ⟨χ, hχ⟩ := prefix_signing_fin_of_transform (euclideanGaussian k) K Good Allowed signingFold
    rules (1/(2*(N : ℝ))) (by positivity) hKmass N hn w hw
  refine ⟨χ, ?_⟩
  intro j hj hjpos
  refine ⟨_, hχ j hj hjpos, ?_⟩
  dsimp only
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [w, smul_smul]
  congr 1
  ring

end Tusnady.Upper
