import Tusnady.EntropyDensityDisintegration

/-! # Entropy of marginal quotients and integrability of conditional entropy -/

open MeasureTheory

namespace Tusnady

/-- Exact scaling identity for the concrete differential entropy integral. -/
theorem densityEntropy_div_scalar {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f : X → ℝ) {p : ℝ} (hp : 0 < p)
    (hfi : Integrable f base) (hflog : Integrable (fun x => f x * Real.log (f x)) base) :
    p * densityEntropy base (fun x => f x / p) =
      densityEntropy base f + Real.log p * ∫ x, f x ∂base := by
  have hpoint (x : X) : (f x / p) * Real.log (f x / p) =
      (f x * Real.log (f x) - Real.log p * f x) / p := by
    by_cases hx : f x = 0
    · simp [hx]
    · rw [Real.log_div hx hp.ne']
      ring
  have hs := integral_sub hflog (hfi.const_mul (Real.log p))
  unfold densityEntropy
  simp_rw [hpoint]
  rw [integral_div, hs, integral_const_mul]
  field_simp
  ring

/-- The entropy of the actual conditional quotient, weighted by its
marginal, including zero prefixes with the fallback density. -/
theorem productConditionalDensity_entropy_weighted {X : Type*} [MeasurableSpace X]
    (g : X × ℝ → ℝ) (hg : ∀ p, 0 ≤ g p)
    (hslice : ∀ x, Integrable (fun y => g (x, y)))
    (hlog : ∀ x, Integrable (fun y => g (x, y) * Real.log (g (x, y)))) (x : X) :
    productDensityMarginal g x * densityEntropy volume (productConditionalDensity g x) =
      -(∫ y, g (x, y) * Real.log (g (x, y))) +
        productDensityMarginal g x * Real.log (productDensityMarginal g x) := by
  classical
  by_cases hx : 0 < productDensityMarginal g x
  · have heq : productConditionalDensity g x = fun y => g (x, y) / productDensityMarginal g x := by
      funext y
      simp [productConditionalDensity, hx]
    rw [heq]
    have h := densityEntropy_div_scalar volume (fun y => g (x, y)) hx (hslice x) (hlog x)
    simpa only [densityEntropy, productDensityMarginal, mul_comm] using h
  · have hm0 : productDensityMarginal g x = 0 :=
      le_antisymm (le_of_not_gt hx) (integral_nonneg fun y => hg (x, y))
    have hzero : (fun y => g (x, y)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => hg (x, y)) (hslice x)).mp hm0
    have hlogzero : (fun y => g (x, y) * Real.log (g (x, y))) =ᵐ[volume] 0 := by
      filter_upwards [hzero] with y hy
      simp [hy]
    rw [hm0, integral_eq_zero_of_ae hlogzero]
    simp

/-- The actual conditional entropy is integrable whenever the pair and
marginal entropy integrands are integrable. This supplies the finiteness
premise of the classical chain identity. -/
theorem productConditionalDensity_entropy_integrable {X : Type*} [MeasurableSpace X]
    (base : Measure X) [SFinite base] (g : X × ℝ → ℝ) (hgm : Measurable g)
    (hg : ∀ p, 0 ≤ g p) (hslice : ∀ x, Integrable (fun y => g (x, y)))
    (hlog : ∀ x, Integrable (fun y => g (x, y) * Real.log (g (x, y))))
    (hjointlog : Integrable (fun p => g p * Real.log (g p)) (base.prod volume))
    (hmarglog : Integrable (fun x => productDensityMarginal g x *
      Real.log (productDensityMarginal g x)) base) :
    Integrable (fun x => densityEntropy volume (productConditionalDensity g x))
      (realDensityMeasure base (productDensityMarginal g)) := by
  apply (integrable_realDensityMeasure_iff base (productDensityMarginal g)
    (fun x => densityEntropy volume (productConditionalDensity g x))
    (productDensityMarginal_measurable hgm)
    (fun x => integral_nonneg fun y => hg (x, y))).mpr
  apply (hjointlog.integral_prod_left.neg.add hmarglog).congr
  exact Filter.Eventually.of_forall fun x =>
    (productConditionalDensity_entropy_weighted g hg hslice hlog x).symm

end Tusnady
