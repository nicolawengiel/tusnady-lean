import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Probability.CDF
import Tusnady.EntropyTransfer
import Mathlib.Tactic

/-!
# The scalar Gini identity

This module proves the scalar symmetrisation in equation (6.5), using
actual integrals against an atomless real probability measure. Its CDF
is written explicitly as `μ.real (Set.Iic x)`.
-/

open MeasureTheory Set

namespace Tusnady

/-- The sign of `x - y`, with value zero on the diagonal. -/
noncomputable def comparisonSign (x y : ℝ) : ℝ :=
  if y < x then 1 else if x < y then -1 else 0

theorem comparisonSign_antisymm (x y : ℝ) :
    comparisonSign y x = -comparisonSign x y := by
  rcases lt_trichotomy x y with h | h | h
  · simp [comparisonSign, h, not_lt.mpr h.le]
  · subst y; simp [comparisonSign]
  · simp [comparisonSign, h, not_lt.mpr h.le]

theorem comparisonSign_mul_sub (x y : ℝ) :
    (x - y) * comparisonSign x y = |x - y| := by
  rcases le_total x y with h | h
  · rcases eq_or_lt_of_le h with rfl | h
    · simp [comparisonSign]
    · simp [comparisonSign, h, not_lt.mpr h.le, abs_of_nonpos (sub_nonpos.mpr h.le)]
  · rcases eq_or_lt_of_le h with h | h
    · subst y; simp [comparisonSign]
    · simp [comparisonSign, h, abs_of_nonneg (sub_nonneg.mpr h.le)]

theorem abs_comparisonSign_le (x y : ℝ) : |comparisonSign x y| ≤ 1 := by
  unfold comparisonSign
  split_ifs <;> norm_num

theorem measurable_comparisonSign :
    Measurable (fun p : ℝ × ℝ => comparisonSign p.1 p.2) := by
  unfold comparisonSign
  exact Measurable.ite (measurableSet_lt measurable_snd measurable_fst)
    measurable_const (Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      measurable_const measurable_const)

theorem integral_comparisonSign (μ : Measure ℝ) [IsProbabilityMeasure μ]
    [NoAtoms μ] (x : ℝ) :
    (∫ y, comparisonSign x y ∂μ) = 2 * μ.real (Iic x) - 1 := by
  have hrepr : (fun y => comparisonSign x y) =
      fun y => (Iio x).indicator (fun _ => (1 : ℝ)) y -
        (Ioi x).indicator (fun _ => (1 : ℝ)) y := by
    funext y
    rcases lt_trichotomy y x with h | h | h
    · simp [comparisonSign, h, not_lt.mpr h.le]
    · subst y; simp [comparisonSign]
    · simp [comparisonSign, h, not_lt.mpr h.le]
  rw [hrepr, integral_sub ((integrable_const (1 : ℝ)).indicator measurableSet_Iio)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi)]
  simp only [integral_indicator_const _ measurableSet_Iio,
    integral_indicator_const _ measurableSet_Ioi, smul_eq_mul, mul_one]
  have hlo : μ.real (Iio x) = μ.real (Iic x) := by
    exact congrArg ENNReal.toReal (measure_congr Iio_ae_eq_Iic)
  have hhi : μ.real (Ioi x) = 1 - μ.real (Iic x) := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, measureReal_univ_eq_one]
  rw [hlo, hhi]
  ring

theorem integrable_weighted_comparisonSign (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun p : ℝ × ℝ => p.1 * comparisonSign p.1 p.2) (μ.prod μ) := by
  apply (hid.comp_fst μ).mono
    (measurable_fst.mul measurable_comparisonSign).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
      mul_le_mul_of_nonneg_left (abs_comparisonSign_le p.1 p.2) (abs_nonneg p.1)

/-- Integrability of the scalar CDF correlation under the finite-first-
moment assumption. -/
theorem integrable_cdf_correlation (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (hid : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun x => x * (2 * ProbabilityTheory.cdf μ x - 1)) μ := by
  apply (integrable_weighted_comparisonSign μ hid).integral_prod_left.congr
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [integral_const_mul, integral_comparisonSign, ProbabilityTheory.cdf_eq_real]

/-- Equation (6.5), for an atomless real probability law with finite first
moment. The CDF and both independent copies are actual measures/integrals. -/
theorem gini_identity (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (hid : Integrable (fun x : ℝ => x) μ) :
    (∫ x, x * (2 * μ.real (Iic x) - 1) ∂μ) =
      (1 / 2 : ℝ) * ∫ p : ℝ × ℝ, |p.1 - p.2| ∂μ.prod μ := by
  let f : ℝ × ℝ → ℝ := fun p => p.1 * comparisonSign p.1 p.2
  have hf : Integrable f (μ.prod μ) := integrable_weighted_comparisonSign μ hid
  have hg : Integrable (fun p : ℝ × ℝ => p.2 * comparisonSign p.1 p.2)
      (μ.prod μ) := by
    apply (hid.comp_snd μ).mono
      (measurable_snd.mul measurable_comparisonSign).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, abs_mul, mul_one] using
        mul_le_mul_of_nonneg_left (abs_comparisonSign_le p.1 p.2) (abs_nonneg p.2)
  have hswap : (∫ p : ℝ × ℝ, p.2 * comparisonSign p.2 p.1 ∂μ.prod μ) =
      ∫ p, f p ∂μ.prod μ := integral_prod_swap f
  have hneg : (∫ p : ℝ × ℝ, p.2 * comparisonSign p.1 p.2 ∂μ.prod μ) =
      -(∫ p, f p ∂μ.prod μ) := by
    calc
      _ = ∫ p : ℝ × ℝ, -(p.2 * comparisonSign p.2 p.1) ∂μ.prod μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          dsimp only
          rw [comparisonSign_antisymm]; ring
      _ = -(∫ p : ℝ × ℝ, p.2 * comparisonSign p.2 p.1 ∂μ.prod μ) := integral_neg _
      _ = _ := congrArg Neg.neg hswap
  have habs : (∫ p : ℝ × ℝ, |p.1 - p.2| ∂μ.prod μ) =
      2 * ∫ p, f p ∂μ.prod μ := by
    calc
      _ = ∫ p : ℝ × ℝ, f p - p.2 * comparisonSign p.1 p.2 ∂μ.prod μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          dsimp [f]
          rw [← sub_mul, comparisonSign_mul_sub]
      _ = (∫ p, f p ∂μ.prod μ) -
          (∫ p : ℝ × ℝ, p.2 * comparisonSign p.1 p.2 ∂μ.prod μ) := integral_sub hf hg
      _ = _ := by rw [hneg]; ring
  have hfirst : (∫ x, x * (2 * μ.real (Iic x) - 1) ∂μ) =
      ∫ p, f p ∂μ.prod μ := by
    rw [integral_prod f hf]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp [f]
      rw [integral_const_mul, integral_comparisonSign]
  rw [hfirst, habs]
  ring

/-- Jensen's mean absolute deviation inequality, with both copies realized
by the product measure. This part does not require atomlessness. -/
theorem mean_abs_deviation_le_gini (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hid : Integrable (fun x : ℝ => x) μ) :
    (∫ x, |x - ∫ y, y ∂μ| ∂μ) ≤
      ∫ p : ℝ × ℝ, |p.1 - p.2| ∂μ.prod μ := by
  have hp : Integrable (fun p : ℝ × ℝ => |p.1 - p.2|) (μ.prod μ) := by
    simpa only [Real.norm_eq_abs] using ((hid.comp_fst μ).sub (hid.comp_snd μ)).norm
  have hm : Integrable (fun x : ℝ => |x - ∫ y, y ∂μ|) μ := by
    simpa only [Real.norm_eq_abs] using (hid.sub (integrable_const (∫ y, y ∂μ))).norm
  have hpoint (x : ℝ) : |x - ∫ y, y ∂μ| ≤ ∫ y, |x - y| ∂μ := by
    have h := norm_integral_le_integral_norm (fun y : ℝ => x - y) (μ := μ)
    simpa only [integral_sub (integrable_const x) hid, integral_const,
      measureReal_univ_eq_one, one_smul, Real.norm_eq_abs] using h
  calc
    _ ≤ ∫ x, ∫ y, |x - y| ∂μ ∂μ := integral_mono hm hp.integral_prod_left hpoint
    _ = _ := (integral_prod _ hp).symm

/-- Nonnegativity of the actual scalar CDF correlation. -/
theorem cdf_correlation_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (hid : Integrable (fun x : ℝ => x) μ) :
    0 ≤ ∫ x, x * (2 * ProbabilityTheory.cdf μ x - 1) ∂μ := by
  simp_rw [ProbabilityTheory.cdf_eq_real]
  rw [gini_identity μ hid]
  exact mul_nonneg (by norm_num) (integral_nonneg fun p => abs_nonneg _)

/-- An atomless probability law has positive absolute deviation from
every center. In particular the Laplace scale used in the manuscript is
strictly positive. -/
theorem absolute_deviation_pos (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    (hid : Integrable (fun x : ℝ => x) μ) (a : ℝ) :
    0 < ∫ x, |x - a| ∂μ := by
  have hi : Integrable (fun x : ℝ => |x - a|) μ := by
    simpa only [Real.norm_eq_abs] using (hid.sub (integrable_const a)).norm
  apply (integral_pos_iff_support_of_nonneg (fun x => abs_nonneg (x - a)) hi).mpr
  have hs : Function.support (fun x : ℝ => |x - a|) = {a}ᶜ := by
    ext x
    simp [Function.mem_support, abs_eq_zero, sub_eq_zero]
  rw [hs]
  have hm : μ ({a}ᶜ) = 1 := by
    simp
  rw [hm]
  exact zero_lt_one

/-- The scalar conclusion (6.6), from the explicitly supplied classical
Laplace maximum-entropy inequality. The new Gini/MAD steps are proved above.
`entropy` must be identified with differential entropy by its caller. -/
theorem scalar_cdf_correlation_of_entropy_bound (μ : Measure ℝ)
    [IsProbabilityMeasure μ] [NoAtoms μ]
    (hid : Integrable (fun x : ℝ => x) μ) (entropy : ℝ)
    (hentropy : entropy ≤ Real.log
      (2 * Real.exp 1 * (∫ x, |x - ∫ y, y ∂μ| ∂μ))) :
    Real.exp entropy / (4 * Real.exp 1) ≤
      ∫ x, x * (2 * ProbabilityTheory.cdf μ x - 1) ∂μ := by
  apply scalar_correlation_of_gini_entropy (absolute_deviation_pos μ hid _) hentropy
  simp_rw [ProbabilityTheory.cdf_eq_real]
  rw [gini_identity μ hid]
  have h := mean_abs_deviation_le_gini μ hid
  linarith

end Tusnady
