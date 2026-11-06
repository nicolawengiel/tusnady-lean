import Tusnady.EntropyDensityLaplace
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Regularity of bounded, compactly supported real densities -/

open MeasureTheory Set
open scoped ENNReal

namespace Tusnady

theorem integrable_of_bounded_supported {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S)
    (hfinite : base S < ∞) (hfm : Measurable f) (C : ℝ)
    (hbound : ∀ x, ‖f x‖ ≤ C) (hzero : ∀ x, x ∉ S → f x = 0) :
    Integrable f base := by
  classical
  have hi : IntegrableOn f S base := IntegrableOn.of_bound hfinite
    hfm.aestronglyMeasurable.restrict C (Filter.Eventually.of_forall hbound)
  have hind := IntegrableOn.integrable_indicator hi hS
  have heq : S.indicator f = f := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx, hzero x hx]
  rwa [heq] at hind

/-- A bounded nonnegative density supported on a finite-measure set has
an integrable entropy integrand, including at zeros of the density. -/
theorem integrable_mul_log_of_bounded_supported {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f : X → ℝ) {S : Set X} (hS : MeasurableSet S)
    (hfinite : base S < ∞) (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    (C : ℝ) (hbound : ∀ x, f x ≤ C) (hzero : ∀ x, x ∉ S → f x = 0) :
    Integrable (fun x => f x * Real.log (f x)) base := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.image Real.continuous_mul_log).isBounded.exists_norm_le
  apply integrable_of_bounded_supported base (fun x => f x * Real.log (f x)) hS hfinite
    (Real.continuous_mul_log.measurable.comp hfm) B
  · intro x
    exact hB _ ⟨f x, ⟨hf x, hbound x⟩, rfl⟩
  · intro x hx
    simp [hzero x hx]

theorem integrable_realDensity_of_bounded_interval (f : ℝ → ℝ)
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x) (C R : ℝ)
    (hbound : ∀ x, f x ≤ C) (hzero : ∀ x, R < |x| → f x = 0) :
    Integrable f := by
  apply integrable_of_bounded_supported volume f measurableSet_Icc
    (isCompact_Icc.measure_lt_top) hfm C
  · intro x
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf x)] using hbound x
  · intro x hx
    apply hzero x
    have : ¬ (-R ≤ x ∧ x ≤ R) := hx
    rw [← abs_le] at this
    exact lt_of_not_ge this

theorem integrable_densityLog_of_bounded_interval (f : ℝ → ℝ)
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x) (C R : ℝ)
    (hbound : ∀ x, f x ≤ C) (hzero : ∀ x, R < |x| → f x = 0) :
    Integrable (fun x => f x * Real.log (f x)) := by
  apply integrable_mul_log_of_bounded_supported volume f measurableSet_Icc
    isCompact_Icc.measure_lt_top hfm hf C hbound
  intro x hx
  apply hzero x
  have : ¬ (-R ≤ x ∧ x ≤ R) := hx
  rw [← abs_le] at this
  exact lt_of_not_ge this

/-- A finite first moment follows from bounded support and integrability;
it is not an additional input of the conditional-density interface. -/
theorem integrable_density_firstMoment_of_supported (f : ℝ → ℝ)
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    {R : ℝ} (_hR : 0 ≤ R) (hzero : ∀ x, R < |x| → f x = 0) :
    Integrable (fun x => f x * x) := by
  apply (hfi.const_mul R).mono' (hfm.mul measurable_id).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (hf x)]
    by_cases hx : |x| ≤ R
    · simpa only [id_eq, mul_comm] using mul_le_mul_of_nonneg_left hx (hf x)
    · rw [hzero x (lt_of_not_ge hx)]
      simp

theorem cdf_realDensityMeasure_eq_integral (f : ℝ → ℝ)
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hnorm : (∫ x, f x) = 1) (x : ℝ) :
    ProbabilityTheory.cdf (realDensityMeasure volume f) x = ∫ y in Iic x, f y := by
  haveI := isProbabilityMeasure_realDensityMeasure volume f hfm hf hfi hnorm
  rw [ProbabilityTheory.cdf_eq_real, Measure.real_def, realDensityMeasure,
    withDensity_apply _ measurableSet_Iic,
    ← ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (Filter.Eventually.of_forall hf),
    ENNReal.toReal_ofReal (integral_nonneg hf)]

/-- Joint measurability of CDFs of a measurable family of actual scalar
probability densities. This is proved by parameter integration. -/
theorem measurable_cdf_realDensityMeasure_family {A : Type*} [MeasurableSpace A]
    (d : A → ℝ → ℝ) (hdm : Measurable (fun p : A × ℝ => d p.1 p.2))
    (hd : ∀ a, ∀ x, 0 ≤ d a x) (hdi : ∀ a, Integrable (d a))
    (hnorm : ∀ a, (∫ x, d a x) = 1) :
    Measurable (fun p : A × ℝ =>
      ProbabilityTheory.cdf (realDensityMeasure volume (d p.1)) p.2) := by
  classical
  have he : Measurable (fun q : (A × ℝ) × ℝ =>
      if q.2 ≤ q.1.2 then d q.1.1 q.2 else 0) := by
    exact Measurable.ite (measurableSet_le measurable_snd measurable_fst.snd)
      (hdm.comp (measurable_fst.fst.prodMk measurable_snd)) measurable_const
  have hi := (he.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
  convert hi using 1
  funext p
  rw [cdf_realDensityMeasure_eq_integral (d p.1)
    (hdm.comp (measurable_const.prodMk measurable_id)) (hd p.1) (hdi p.1) (hnorm p.1)]
  rw [← integral_indicator measurableSet_Iic]
  congr 1

end Tusnady
