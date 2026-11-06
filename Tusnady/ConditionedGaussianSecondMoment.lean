import Tusnady.ConditionedGaussianTilt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact second moment of a conditioned Gaussian

This proves Main.pdf Lemma 2.4 through Anderson's inequality and Gaussian
tilting, rather than the radial-coordinate proof printed in the paper.
The statement and constants are unchanged; the sole literature dependency
is the already declared Anderson inequality.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace Tusnady

theorem one_add_half_sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := Summable.sum_le_tsum (Finset.range 2)
    (fun n _ => div_nonneg (by rw [pow_mul]; exact pow_nonneg (sq_nonneg x) n)
      (Nat.cast_nonneg _) : ∀ n ∉ Finset.range 2, 0 ≤ x ^ (2 * n) / ((2 * n).factorial : ℝ))
    (Real.hasSum_cosh x).summable
  rw [(Real.hasSum_cosh x).tsum_eq] at h
  norm_num [Finset.sum_range_succ] at h
  exact h

theorem conditionedGaussian_cosh_integral_le {M : ℕ} (anderson : Literature.Anderson)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hsymm : ∀ z : Fin M → ℝ, z ∈ K ↔ -z ∈ K)
    (hp : 0 < gaussianConditioningMass M K) (j : Fin M) (t : ℝ) :
    (∫ z, Real.cosh (t * z j) ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) ≤
      Real.exp (t ^ 2 / 2) := by
  have hpos := conditionedGaussian_exp_integral_le anderson hK hconvex hsymm hp j t
  have hneg := conditionedGaussian_exp_integral_le anderson hK hconvex hsymm hp j (-t)
  have heq : (-t) ^ 2 = t ^ 2 := by ring
  rw [heq] at hneg
  have hipos := conditionedGaussian_test_integrable M hK hp (fun z => Real.exp (t * z j)) (by fun_prop)
  have hineg := conditionedGaussian_test_integrable M hK hp (fun z => Real.exp ((-t) * z j)) (by fun_prop)
  have hfun : (fun z : Fin M → ℝ => Real.cosh (t * z j)) =
      fun z => (Real.exp (t * z j) + Real.exp ((-t) * z j)) / 2 := by
    funext z
    rw [Real.cosh_eq, neg_mul]
  rw [hfun, integral_div, integral_add hipos hineg]
  linarith

theorem conditionedGaussian_cosh_integral_lower {M : ℕ} {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K) (j : Fin M) (t : ℝ) :
    1 + (t ^ 2 / 2) *
      (∫ z, (z j) ^ 2 ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) ≤
      ∫ z, Real.cosh (t * z j) ∂ProbabilityTheory.cond (Literature.standardGaussian M) K := by
  let ν := ProbabilityTheory.cond (Literature.standardGaussian M) K
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    rw [← conditionedGaussianConditionalSystem_law M hK hp]
    infer_instance
  have hsq : Integrable (fun z : Fin M → ℝ => (z j) ^ 2) ν :=
    conditionedGaussian_test_integrable M hK hp (fun z => (z j) ^ 2) (by fun_prop)
  have hcosh : Integrable (fun z : Fin M → ℝ => Real.cosh (t * z j)) ν :=
    conditionedGaussian_test_integrable M hK hp (fun z => Real.cosh (t * z j)) (by fun_prop)
  have hI : (∫ z : Fin M → ℝ, 1 + (t ^ 2 / 2) * (z j) ^ 2 ∂ν) ≤
      ∫ z, Real.cosh (t * z j) ∂ν := by
    apply integral_mono ((integrable_const (1 : ℝ)).add (hsq.const_mul (t ^ 2 / 2))) hcosh
    intro z
    change 1 + (t ^ 2 / 2) * (z j) ^ 2 ≤ Real.cosh (t * z j)
    have h := one_add_half_sq_le_cosh (t * z j)
    nlinarith
  rw [integral_add (f := fun _ : Fin M → ℝ => (1 : ℝ))
    (g := fun z => (t ^ 2 / 2) * (z j) ^ 2) (integrable_const _) (hsq.const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at hI
  exact hI

/-- Each coordinate's conditional second moment is at most one. -/
theorem conditionedGaussian_coordinate_secondMoment {M : ℕ} (anderson : Literature.Anderson)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hsymm : ∀ z : Fin M → ℝ, z ∈ K ↔ -z ∈ K)
    (hp : 0 < gaussianConditioningMass M K) (j : Fin M) :
    (∫ z, (z j) ^ 2 ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) ≤ 1 := by
  let moment : ℝ := ∫ z, (z j) ^ 2 ∂ProbabilityTheory.cond (Literature.standardGaussian M) K
  have hbound (h : ℝ) (hh : 0 < h) : moment ≤ (Real.exp h - 1) / h := by
    let t := Real.sqrt (2 * h)
    have ht : t ^ 2 / 2 = h := by
      dsimp [t]
      rw [Real.sq_sqrt (by positivity)]
      ring
    have hlo := conditionedGaussian_cosh_integral_lower hK hp j t
    have hhi := conditionedGaussian_cosh_integral_le anderson hK hconvex hsymm hp j t
    rw [ht] at hlo hhi
    apply (le_div_iff₀ hh).mpr
    linarith
  have hlim : Tendsto (fun h : ℝ => (Real.exp h - 1) / h) (𝓝[>] 0) (𝓝 1) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  have hneg := le_of_tendsto hlim.neg (show ∀ᶠ h : ℝ in 𝓝[>] 0,
      -((Real.exp h - 1) / h) ≤ -moment from by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact neg_le_neg (hbound h hh))
  linarith

/-- Main.pdf Lemma 2.4 with the exact constant `M`, for the actual
conditioned Gaussian measure and actual squared Euclidean energy. -/
theorem conditionedGaussian_secondMoment (M : ℕ) (anderson : Literature.Anderson)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hsymm : ∀ z : Fin M → ℝ, z ∈ K ↔ -z ∈ K)
    (hp : 0 < gaussianConditioningMass M K) :
    (∫ z, gaussianEnergy M z ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) ≤ M := by
  unfold gaussianEnergy
  rw [integral_finset_sum Finset.univ (fun j _ =>
    conditionedGaussian_test_integrable M hK hp (fun z => (z j) ^ 2) (by fun_prop))]
  calc
    _ ≤ ∑ _j : Fin M, (1 : ℝ) := Finset.sum_le_sum fun j _ =>
      conditionedGaussian_coordinate_secondMoment anderson hK hconvex hsymm hp j
    _ = M := by simp

end Tusnady
