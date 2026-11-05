import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Verified kernels for the entropy obstruction

These are components of Proposition 6.3, **not** a proof of Proposition 6.2
or of the main theorem. In particular no Rosenblatt correlation theorem is
postulated here. The moment and correlation inputs in the statements remain
explicit mathematical hypotheses of these component lemmas.
-/

open scoped BigOperators InnerProductSpace
open MeasureTheory

namespace Tusnady

/-- The numerical implication used after the scalar Gini identity and
the Laplace maximum-entropy inequality in Prop. 6.2. The probabilistic
identities themselves are not asserted by this lemma. -/
theorem scalar_correlation_of_gini_entropy {entropy beta corr : ℝ}
    (hbeta : 0 < beta)
    (hentropy : entropy ≤ Real.log (2 * Real.exp 1 * beta))
    (hgini : beta / 2 ≤ corr) :
    Real.exp entropy / (4 * Real.exp 1) ≤ corr := by
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  have hpos : 0 < 2 * Real.exp 1 * beta := by positivity
  have he := (Real.le_log_iff_exp_le hpos).mp hentropy
  apply (div_le_iff₀ (by positivity : 0 < 4 * Real.exp 1)).mpr
  nlinarith

/-- Nonnegative coordinate correlations may be weighted from below by their
smallest response coefficient. This is the finite-sum step in Prop. 6.3. -/
theorem weighted_correlation_lower_bound {ι : Type*} [Fintype ι]
    (weight corr : ι → ℝ) {s : ℝ}
    (hcorr : ∀ i, 0 ≤ corr i) (hweight : ∀ i, s ≤ weight i) :
    s * ∑ i, corr i ≤ ∑ i, weight i * corr i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hweight i) (hcorr i)

/-- The algebraic conclusion of Prop. 6.3, with all inputs visible.
`corr i` is intended to be `E[Z_i U_i]` and `err` to be `E[Z · e(U)]`.
This lemma does not establish either interpretation or the input bounds. -/
theorem small_ball_obstruction_core {ι : Type*} [Fintype ι]
    (weight corr : ι → ℝ) {s c rho mass t err : ℝ}
    (hs : 0 ≤ s) (hcorr : ∀ i, 0 ≤ corr i)
    (hweight : ∀ i, s ≤ weight i)
    (hcorrelation : c * mass ≤ ∑ i, corr i)
    (herror : -(rho * s * mass) ≤ err)
    (hupper : (∑ i, weight i * corr i) + err ≤ t) :
    (c - rho) * s * mass ≤ t := by
  have hw := weighted_correlation_lower_bound weight corr hcorr hweight
  have hc := mul_le_mul_of_nonneg_left hcorrelation hs
  nlinarith

/-- Cauchy--Schwarz with second-moment bounds, in any real inner-product
space. Applied in `L²`, it controls dependent random vectors as well. -/
theorem inner_lower_of_second_moments {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z e : E) {mass q : ℝ} (hmass : 0 ≤ mass) (hq : 0 ≤ q)
    (hz : ‖z‖ ^ 2 ≤ mass) (he : ‖e‖ ^ 2 ≤ q ^ 2 * mass) :
    -(q * mass) ≤ inner ℝ z e := by
  have hp : (‖z‖ * ‖e‖) ^ 2 ≤ (q * mass) ^ 2 := by
    calc
      (‖z‖ * ‖e‖) ^ 2 = ‖z‖ ^ 2 * ‖e‖ ^ 2 := by ring
      _ ≤ mass * (q ^ 2 * mass) := mul_le_mul hz he (sq_nonneg _) hmass
      _ = (q * mass) ^ 2 := by ring
  have hn : ‖z‖ * ‖e‖ ≤ q * mass := by
    have hnz := norm_nonneg z
    have hne := norm_nonneg e
    have hprod : 0 ≤ ‖z‖ * ‖e‖ := mul_nonneg hnz hne
    have hqm : 0 ≤ q * mass := mul_nonneg hq hmass
    nlinarith
  have hi := abs_real_inner_le_norm z e
  have hlo := neg_abs_le (inner ℝ z e)
  linarith

/-- The actual integral form of the error estimate in Prop. 6.3.
The two vectors live on the same probability space; no independence
assumption is present. The theorem holds for any measure. -/
theorem integral_error_lower_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure Ω} (Z err : Lp E 2 μ) {mass q : ℝ}
    (hmass : 0 ≤ mass) (hq : 0 ≤ q)
    (hz : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤ mass)
    (he : (∫ ω, ‖err ω‖ ^ 2 ∂μ) ≤ q ^ 2 * mass) :
    -(q * mass) ≤ ∫ ω, inner ℝ (Z ω) (err ω) ∂μ := by
  have hz' : ‖Z‖ ^ 2 ≤ mass := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simpa only [real_inner_self_eq_norm_sq] using hz
  have he' : ‖err‖ ^ 2 ≤ q ^ 2 * mass := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simpa only [real_inner_self_eq_norm_sq] using he
  simpa only [L2.inner_def] using
    inner_lower_of_second_moments Z err hmass hq hz' he'

/-- Prop. 6.3's sum and integral calculation, assuming its correlation
and response bounds. The missing Rosenblatt/entropy argument and the
construction producing these inputs are not hypotheses of a main theorem. -/
theorem small_ball_obstruction_l2 {Ω E ι : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    {μ : Measure Ω} (Z err : Lp E 2 μ) (weight corr : ι → ℝ)
    {s c rho mass t : ℝ} (hs : 0 ≤ s) (hrho : 0 ≤ rho)
    (hmass : 0 ≤ mass) (hcorr : ∀ i, 0 ≤ corr i)
    (hweight : ∀ i, s ≤ weight i)
    (hcorrelation : c * mass ≤ ∑ i, corr i)
    (hz : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤ mass)
    (he : (∫ ω, ‖err ω‖ ^ 2 ∂μ) ≤ (rho * s) ^ 2 * mass)
    (hupper : (∑ i, weight i * corr i) +
      (∫ ω, inner ℝ (Z ω) (err ω) ∂μ) ≤ t) :
    (c - rho) * s * mass ≤ t := by
  apply small_ball_obstruction_core weight corr hs hcorr hweight hcorrelation
  · simpa only [mul_assoc] using
      integral_error_lower_bound Z err hmass (mul_nonneg hrho hs) hz he
  · exact hupper

/-- Absorbing the decaying error, as in Prop. 7.2. -/
theorem absorb_small_error {D c rho s mass : ℝ}
    (hs : 0 ≤ s) (hmass : 0 ≤ mass) (hrho : rho ≤ c / 2)
    (hbound : (c - rho) * s * mass ≤ 2 * D) :
    (c / 4) * s * mass ≤ D := by
  have hsm : 0 ≤ s * mass := mul_nonneg hs hmass
  have h := mul_le_mul_of_nonneg_right hrho hsm
  nlinarith

end Tusnady
