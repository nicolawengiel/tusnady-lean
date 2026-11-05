import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Differential entropy of an actual density

The definition is the manuscript's `-∫ f log f`. Entropy theorems require
the integrability conditions explicitly, so the default value of the
Bochner integral is never used as an entropy existence assertion.
-/

open MeasureTheory

namespace Tusnady

/-- Differential entropy relative to a specified reference measure.
For Lebesgue differential entropy the reference measure is `volume`. -/
noncomputable def densityEntropy {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f : X → ℝ) : ℝ :=
  -(∫ x, f x * Real.log (f x) ∂base)

/-- Pointwise Gibbs inequality in density coordinates. It is derived
from mathlib's nonnegative function `u log u + 1 - u`, including `f=0`. -/
theorem density_gibbs_pointwise {f g : ℝ} (hf : 0 ≤ f) (hg : 0 < g) :
    0 ≤ f * Real.log f - f * Real.log g + g - f := by
  have hk := mul_nonneg hg.le
    (InformationTheory.klFun_nonneg (div_nonneg hf hg.le))
  have hid : g * InformationTheory.klFun (f / g) =
      f * Real.log f - f * Real.log g + g - f := by
    by_cases hf0 : f = 0
    · simp [hf0, InformationTheory.klFun]
    · rw [InformationTheory.klFun, Real.log_div hf0 hg.ne']
      field_simp
  rwa [hid] at hk

/-- Gibbs' inequality for two actual normalized real densities.
All analytic hypotheses are stated directly. -/
theorem densityEntropy_le_crossEntropy {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f g : X → ℝ)
    (hf : ∀ᵐ x ∂base, 0 ≤ f x) (hg : ∀ᵐ x ∂base, 0 < g x)
    (hfi : Integrable f base) (hgi : Integrable g base)
    (hflog : Integrable (fun x => f x * Real.log (f x)) base)
    (hcross : Integrable (fun x => f x * Real.log (g x)) base)
    (hfnorm : (∫ x, f x ∂base) = 1) (hgnorm : (∫ x, g x ∂base) = 1) :
    densityEntropy base f ≤ -(∫ x, f x * Real.log (g x) ∂base) := by
  have hp : 0 ≤ ∫ x, (((fun x => f x * Real.log (f x)) -
      (fun x => f x * Real.log (g x))) + g - f) x ∂base := by
    apply integral_nonneg_of_ae
    filter_upwards [hf, hg] with x hfx hgx
    exact density_gibbs_pointwise hfx hgx
  have hs := integral_sub ((hflog.sub hcross).add hgi) hfi
  have ha := integral_add (hflog.sub hcross) hgi
  have hs' := integral_sub hflog hcross
  simp only [Pi.sub_apply, Pi.add_apply] at hp hs ha hs'
  rw [hs, ha, hs', hfnorm, hgnorm] at hp
  unfold densityEntropy
  linarith

/-- The measure having real nonnegative density `f` with respect to `base`.
Nonnegativity is required by every interpretation lemma below. -/
noncomputable def realDensityMeasure {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f : X → ℝ) : Measure X :=
  base.withDensity (fun x => ENNReal.ofReal (f x))

/-- Change of density for the concrete real density representation. -/
theorem integral_realDensityMeasure {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f h : X → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) :
    (∫ x, h x ∂realDensityMeasure base f) = ∫ x, f x * h x ∂base := by
  rw [realDensityMeasure, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (hf _), smul_eq_mul]
  · exact hfm.ennreal_ofReal
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

/-- Integrability after change of density, stated as an equivalence. -/
theorem integrable_realDensityMeasure_iff {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f h : X → ℝ) (hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) :
    Integrable h (realDensityMeasure base f) ↔ Integrable (fun x => f x * h x) base := by
  rw [realDensityMeasure, integrable_withDensity_iff_integrable_smul'
    hfm.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf _), smul_eq_mul]

/-- A normalized nonnegative real density determines a probability law. -/
theorem isProbabilityMeasure_realDensityMeasure {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f : X → ℝ) (_hfm : Measurable f)
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f base)
    (hfnorm : (∫ x, f x ∂base) = 1) :
    IsProbabilityMeasure (realDensityMeasure base f) := by
  constructor
  rw [realDensityMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf), hfnorm]
  norm_num

end Tusnady
