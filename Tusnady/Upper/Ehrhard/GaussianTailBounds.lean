import Tusnady.Upper.Ehrhard.Quantile

/-!
# Elementary one-dimensional Gaussian tail bound

The Mills upper bound is proved directly by integrating the Gaussian density
derivative. It will be used in the half-plane fold estimate.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OAI.GaussianPropeller.Quantile

lemma integrable_mul_φ : Integrable (fun x : ℝ => x * φ x) := by
  have hi := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).const_mul
    ((Real.sqrt (2*Real.pi))⁻¹)
  convert hi using 1
  funext x
  simp only [φ]
  rw [show -x^2/2 = -(1/2 : ℝ)*x^2 by ring]
  ring

lemma tendsto_φ_atTop : Tendsto φ atTop (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ => Real.exp (-(1/2 : ℝ)*x^2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by norm_num : (-(1/2 : ℝ)) < 0))
  convert ht.const_mul ((Real.sqrt (2*Real.pi))⁻¹) using 1
  · funext x
    unfold φ
    congr 2
    ring
  · simp

lemma right_first_moment (a : ℝ) : ∫ x in Ioi a, x * φ x = φ a := by
  have hd (x : ℝ) : HasDerivAt (fun x => -φ x) (x * φ x) x := by
    convert (hasDerivAt_φ x).neg using 1
    ring
  simpa only [neg_zero, sub_neg_eq_add, zero_add, Pi.neg_apply] using
    integral_Ioi_of_hasDerivAt_of_tendsto (continuous_φ.neg.continuousWithinAt)
      (fun x _ => hd x) integrable_mul_φ.integrableOn tendsto_φ_atTop.neg

lemma gaussian_tail_eq_integral (a : ℝ) : Φ (-a) = ∫ x in Ioi a, φ x := by
  rw [Φ_neg, Φ_eq_one_sub_tail]
  ring

/-- Mills' bound for the actual integral-defined normal distribution. -/
theorem gaussian_tail_le_density_div {a : ℝ} (ha : 0 < a) : Φ (-a) ≤ φ a / a := by
  rw [gaussian_tail_eq_integral]
  calc
    _ ≤ ∫ x in Ioi a, (x * φ x) / a := by
      apply integral_mono_ae integrable_φ.integrableOn (integrable_mul_φ.div_const a).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      apply (le_div_iff₀ ha).mpr
      nlinarith [(φ_pos x).le, mul_le_mul_of_nonneg_right hx.le (φ_pos x).le]
    _ = φ a / a := by rw [integral_div, right_first_moment]

end OAI.GaussianPropeller.Quantile
