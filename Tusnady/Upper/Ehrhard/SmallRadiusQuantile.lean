import Tusnady.Upper.Ehrhard.GaussianBallAsymptotics
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit small-radius Gaussian quantiles

All numerical bounds below are proved from mathlib's proved bounds on pi and
exp(1).  The final statement uses the actual standard Gaussian interval mass.
The deliberately conservative radius 1/1000 gives a universal signing constant
without assuming a numerical assertion from the literature.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace OAI.GaussianPropeller.SmallRadiusQuantile
open Quantile

/-- Actual standard Gaussian mass of the centered closed interval. -/
def intervalMass (r : ℝ) : ℝ := (gaussianReal 0 1).real (Icc (-r) r)

lemma intervalMass_eq_integral (r : ℝ) :
    intervalMass r = ∫ x in Icc (-r) r, φ x := by
  rw [intervalMass, measureReal_def,
    gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

lemma density_zero_le_half : φ 0 ≤ (1 : ℝ) / 2 := by
  have hspos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsq : (Real.sqrt (2 * Real.pi))^2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hs : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by nlinarith [Real.pi_gt_three]
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hs
  simpa only [φ, zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_div, Real.exp_zero,
    mul_one, one_div] using hh

lemma density_le_half (x : ℝ) : φ x ≤ (1 : ℝ) / 2 := (φ_le_zero x).trans density_zero_le_half

lemma intervalMass_pos {r : ℝ} (hr : 0 < r) : 0 < intervalMass r := by
  rw [intervalMass_eq_integral]
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun x => (φ_pos x).le)) integrable_φ.integrableOn).mpr
  have hs : Function.support φ = univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (φ_pos x)]
  rw [hs, univ_inter, Real.volume_Icc, ENNReal.ofReal_pos]
  linarith

lemma intervalMass_le_radius {r : ℝ} (hr : 0 ≤ r) : intervalMass r ≤ r := by
  have hv : (volume : Measure ℝ).real (Icc (-r) r) = 2 * r := by
    simp only [measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := φ)
    (s := Icc (-r) r) (C := (1 : ℝ) / 2) (by simp)
    (fun x _ => by rw [Real.norm_eq_abs, abs_of_pos (φ_pos x)]; exact density_le_half x)
  have hp : 0 ≤ ∫ x in Icc (-r) r, φ x := integral_nonneg (fun x => (φ_pos x).le)
  rw [Real.norm_eq_abs, abs_of_nonneg hp, hv] at hb
  rw [intervalMass_eq_integral]
  linarith

lemma cdf_increment_le (u : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Φ (u + r) ≤ Φ u + r / 2 := by
  have hv : (volume : Measure ℝ).real (Ioc u (u + r)) = r := by
    simp only [measureReal_def, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    ring
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := φ)
    (s := Ioc u (u + r)) (C := (1 : ℝ) / 2) (by simp)
    (fun x _ => by rw [Real.norm_eq_abs, abs_of_pos (φ_pos x)]; exact density_le_half x)
  have hi := intervalIntegral.integral_Iic_sub_Iic (a := u) (b := u + r)
    integrable_φ.integrableOn integrable_φ.integrableOn
  change Φ (u + r) - Φ u = _ at hi
  rw [intervalIntegral.integral_of_le (by linarith)] at hi
  rw [Real.norm_eq_abs, hv, ← hi] at hb
  have hh := (le_abs_self (Φ (u + r) - Φ u)).trans hb
  linarith

/-- A proved coarse rational lower bound, not a numerical premise. -/
lemma density_three_add_gt {r : ℝ} (hr : 0 < r) (hsmall : r ≤ (1 : ℝ) / 1000) :
    (1 : ℝ) / 729 < φ (3 + r) := by
  have hspos : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hsq : (Real.sqrt (2 * Real.pi))^2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hslt : Real.sqrt (2 * Real.pi) < 3 := by nlinarith [Real.pi_lt_four]
  have hn : (1 : ℝ) / 3 < (Real.sqrt (2 * Real.pi))⁻¹ := by
    simpa only [one_div] using one_div_lt_one_div_of_lt hspos hslt
  have heone : Real.exp 1 < (3 : ℝ) := by linarith [Real.exp_one_lt_d9]
  have hepow := pow_lt_pow_left₀ heone (Real.exp_pos 1).le (by norm_num : 5 ≠ 0)
  have hefive : Real.exp 5 < (243 : ℝ) := by
    have heq : (Real.exp 1)^5 = Real.exp 5 := by
      simpa using (Real.exp_nat_mul 1 5).symm
    rw [heq] at hepow
    norm_num at hepow
    exact hepow
  have hrsq : r^2 ≤ ((1 : ℝ) / 1000)^2 := pow_le_pow_left₀ hr.le hsmall 2
  have hu : (3 + r)^2 / 2 < (5 : ℝ) := by nlinarith
  have he : Real.exp ((3 + r)^2 / 2) < (243 : ℝ) :=
    (Real.exp_lt_exp.mpr hu).trans hefive
  have heinv : (1 : ℝ) / 243 < Real.exp (-(3 + r)^2 / 2) := by
    have hh := one_div_lt_one_div_of_lt (Real.exp_pos ((3 + r)^2 / 2)) he
    have hneg : -(3 + r)^2 / 2 = -((3 + r)^2 / 2) := by ring
    rw [hneg, Real.exp_neg]
    simpa only [one_div] using hh
  have hmul₁ := mul_lt_mul_of_pos_right hn (by norm_num : (0 : ℝ) < 1 / 243)
  have hmul₂ := mul_lt_mul_of_pos_left heinv (inv_pos.mpr hspos)
  have hh := hmul₁.trans hmul₂
  rw [show (1 / 3 : ℝ) * (1 / 243) = 1 / 729 by norm_num] at hh
  exact hh

lemma cdf_negative_two_add_gt_radius {r : ℝ} (hr : 0 < r)
    (hsmall : r ≤ (1 : ℝ) / 1000) : r < Φ (-(2 + r)) := by
  have hd := density_three_add_gt hr hsmall
  have ht := one_sub_Φ_ge_density_add_one (by linarith : 0 ≤ (2 : ℝ) + r)
  rw [show (2 : ℝ) + r + 1 = 3 + r by ring, ← Φ_neg (2 + r)] at ht
  have hrsmall : r < (1 : ℝ) / 729 := by linarith
  exact hrsmall.trans_le (hd.le.trans ht)

/-- A fully quantified small-radius form of the Gaussian quantile estimate.
The probability and the quantile are the actual defined quantities, with no
Gaussian, numerical or isoperimetric assumption in addition to the radius bound. -/
theorem small_radius_quantile {r : ℝ} (hr : 0 < r) (hsmall : r ≤ (1 : ℝ) / 1000) :
    let pr := (gaussianReal 0 1).real (Icc (-r) r)
    let w := -Quantile.q pr
    pr ∈ Ioo (0 : ℝ) 1 ∧ 2 ≤ w - r ∧ Φ (-w + r) ≤ r * (w - r) := by
  change intervalMass r ∈ Ioo (0 : ℝ) 1 ∧
    2 ≤ -q (intervalMass r) - r ∧
    Φ (-(-q (intervalMass r)) + r) ≤ r * (-q (intervalMass r) - r)
  have hp_le := intervalMass_le_radius hr.le
  have hp : intervalMass r ∈ Ioo (0 : ℝ) 1 :=
    ⟨intervalMass_pos hr, by linarith⟩
  have hlt : q (intervalMass r) < -(2 + r) := by
    apply strictMono_Φ.lt_iff_lt.mp
    rw [Φ_q hp]
    exact hp_le.trans_lt (cdf_negative_two_add_gt_radius hr hsmall)
  have hw : 2 ≤ -q (intervalMass r) - r := by linarith
  refine ⟨hp, hw, ?_⟩
  have hinc := cdf_increment_le (q (intervalMass r)) hr.le
  rw [Φ_q hp] at hinc
  have hmul := mul_le_mul_of_nonneg_left hw hr.le
  simp only [neg_neg]
  nlinarith

end OAI.GaussianPropeller.SmallRadiusQuantile
