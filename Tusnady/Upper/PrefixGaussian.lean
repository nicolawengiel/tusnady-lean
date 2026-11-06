import Tusnady.Upper.GaussianBody
import Tusnady.Upper.PrefixFoldGeometry
import Mathlib.Tactic.FieldSimp

/-!
# Exact open analytic input and its proved prefix consequence

`GaussianFoldMonotonicity` is a named OPEN proposition, not an axiom and not a
proved theorem.  Its concrete fold and its actual Gaussian measure are fixed
below.  Every theorem in this file retains this input as an explicit argument.
Consequently these theorems must not be reported as an unconditional proof of
Nikolov's Lemma 9.

Analytic source: Banaszczyk (1998), Theorem 3; see also Garg (2018), Chapter 3,
Theorem 15, printed pp. 18--24.  The prefix consequence matches Nikolov (2017),
Lemma 9: Gaussian mass at least `1 - 1/(2N)`, vectors of norm at most one,
one fixed choice of signs, and every prefix in `5K`.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Tusnady.Upper

/-- OPEN: Gaussian measure monotonicity of the actual closed Banaszczyk fold.
There is deliberately no declaration proving or postulating this proposition.
Symmetry is the only version needed in the subsequent prefix recursion. -/
def GaussianFoldMonotonicity : Prop :=
  ∀ k : ℕ, ∀ K : Set (EuclideanSpace ℝ (Fin k)),
    IsCompact K → Convex ℝ K → (∀ x ∈ K, -x ∈ K) →
    ∀ u : EuclideanSpace ℝ (Fin k), ‖u‖ ≤ (1 : ℝ) / 5 →
      (1 : ℝ) / 2 ≤ (euclideanGaussian k).real K →
      (euclideanGaussian k).real K ≤ (euclideanGaussian k).real (signingFold u K)

/-- All bookkeeping, geometry and simultaneous prefix selection are discharged;
the explicitly named analytic proposition is the only literature input here. -/
theorem prefix_signing_small_of_gaussianFoldMonotonicity
    (hfold : GaussianFoldMonotonicity) {k N : ℕ} (hN : 0 < N)
    (K : Set (EuclideanSpace ℝ (Fin k))) (hKcomp : IsCompact K)
    (hKconv : Convex ℝ K) (hKsymm : ∀ x ∈ K, -x ∈ K)
    (hKmass : 1 - 1 / (2 * (N : ℝ)) ≤ (euclideanGaussian k).real K)
    (v : Fin N → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ ≤ (1 : ℝ) / 5) :
    ∃ χ : Fin N → Bool, ∀ j (hj : j ≤ N), 0 < j →
      (∑ i : Fin j,
        Tusnady.sign (χ ⟨i.val, lt_of_lt_of_le i.isLt hj⟩) •
          v ⟨i.val, lt_of_lt_of_le i.isLt hj⟩) ∈ K := by
  let Good : Set (EuclideanSpace ℝ (Fin k)) → Prop :=
    fun A => IsClosed A ∧ Convex ℝ A ∧ ∀ x ∈ A, -x ∈ A
  let Allowed : EuclideanSpace ℝ (Fin k) → Prop := fun u => ‖u‖ ≤ (1 : ℝ) / 5
  have rules : TransformRules (euclideanGaussian k) K Good Allowed signingFold :=
    signingFold_transformRules (euclideanGaussian k) K hKcomp hKconv hKsymm Allowed
      (hfold k)
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hn : (N : ℝ) * (1 / (2 * (N : ℝ))) ≤ (1 : ℝ) / 2 := by
    field_simp
    norm_num
  exact prefix_signing_fin_of_transform (euclideanGaussian k) K Good Allowed signingFold
    rules (1 / (2 * (N : ℝ))) (by positivity) hKmass N hn v hv

/-- The exact scaling in Nikolov's Lemma 9.  Its open analytic hypothesis is
retained visibly in the theorem type; no independent signs are chosen for
different prefix lengths. -/
theorem prefix_signing_of_gaussianFoldMonotonicity
    (hfold : GaussianFoldMonotonicity) {k N : ℕ} (hN : 0 < N)
    (K : Set (EuclideanSpace ℝ (Fin k))) (hKcomp : IsCompact K)
    (hKconv : Convex ℝ K) (hKsymm : ∀ x ∈ K, -x ∈ K)
    (hKmass : 1 - 1 / (2 * (N : ℝ)) ≤ (euclideanGaussian k).real K)
    (v : Fin N → EuclideanSpace ℝ (Fin k)) (hv : ∀ i, ‖v i‖ ≤ 1) :
    ∃ χ : Fin N → Bool, ∀ j (hj : j ≤ N), 0 < j →
      (∑ i : Fin j,
        Tusnady.sign (χ ⟨i.val, lt_of_lt_of_le i.isLt hj⟩) •
          v ⟨i.val, lt_of_lt_of_le i.isLt hj⟩) ∈
        (fun x : EuclideanSpace ℝ (Fin k) => (5 : ℝ) • x) '' K := by
  let w : Fin N → EuclideanSpace ℝ (Fin k) := fun i => (1 / 5 : ℝ) • v i
  have hw : ∀ i, ‖w i‖ ≤ (1 : ℝ) / 5 := by
    intro i
    simpa only [w, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 5),
      mul_one] using mul_le_mul_of_nonneg_left (hv i) (by norm_num : (0 : ℝ) ≤ 1 / 5)
  obtain ⟨χ, hχ⟩ := prefix_signing_small_of_gaussianFoldMonotonicity hfold hN K
    hKcomp hKconv hKsymm hKmass w hw
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
