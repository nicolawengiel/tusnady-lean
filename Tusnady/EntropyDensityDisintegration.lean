import Tusnady.EntropyDensityBounded
import Mathlib.MeasureTheory.Integral.Prod

/-! # Conditional scalar densities by marginal quotient and null fallback -/

open MeasureTheory Set

namespace Tusnady

/-- A fixed normalized compactly supported density used only when the
marginal is zero. -/
noncomputable def nullPrefixDensity : ℝ → ℝ := (Icc (0 : ℝ) 1).indicator (fun _ => 1)

theorem nullPrefixDensity_measurable : Measurable nullPrefixDensity :=
  measurable_const.indicator measurableSet_Icc

theorem nullPrefixDensity_nonneg (y : ℝ) : 0 ≤ nullPrefixDensity y := by
  exact indicator_nonneg (fun _ _ => zero_le_one) y

theorem nullPrefixDensity_le_one (y : ℝ) : nullPrefixDensity y ≤ 1 := by
  classical
  by_cases hy : y ∈ Icc (0 : ℝ) 1 <;> simp [nullPrefixDensity, hy]

theorem nullPrefixDensity_zero {y : ℝ} (hy : 1 < |y|) : nullPrefixDensity y = 0 := by
  apply indicator_of_notMem
  intro h
  have habs : |y| ≤ 1 := abs_le.mpr ⟨by linarith [h.1], h.2⟩
  linarith

theorem integral_nullPrefixDensity : (∫ y, nullPrefixDensity y) = 1 := by
  rw [nullPrefixDensity, integral_indicator measurableSet_Icc]
  simp

noncomputable def productDensityMarginal {X : Type*} [MeasurableSpace X]
    (g : X × ℝ → ℝ) (x : X) : ℝ := ∫ y, g (x, y)

noncomputable def productConditionalDensity {X : Type*} [MeasurableSpace X]
    (g : X × ℝ → ℝ) (x : X) (y : ℝ) : ℝ :=
  if 0 < productDensityMarginal g x then g (x, y) / productDensityMarginal g x
  else nullPrefixDensity y

theorem productDensityMarginal_measurable {X : Type*} [MeasurableSpace X]
    {g : X × ℝ → ℝ} (hgm : Measurable g) : Measurable (productDensityMarginal g) :=
  hgm.stronglyMeasurable.integral_prod_right'.measurable

theorem productConditionalDensity_measurable {X : Type*} [MeasurableSpace X]
    {g : X × ℝ → ℝ} (hgm : Measurable g) :
    Measurable (fun p : X × ℝ => productConditionalDensity g p.1 p.2) := by
  unfold productConditionalDensity
  exact Measurable.ite
    (measurableSet_lt measurable_const ((productDensityMarginal_measurable hgm).comp measurable_fst))
    (hgm.div ((productDensityMarginal_measurable hgm).comp measurable_fst))
    (nullPrefixDensity_measurable.comp measurable_snd)

theorem productConditionalDensity_nonneg {X : Type*} [MeasurableSpace X]
    {g : X × ℝ → ℝ} (hg : ∀ p, 0 ≤ g p) (x : X) (y : ℝ) :
    0 ≤ productConditionalDensity g x y := by
  unfold productConditionalDensity
  split_ifs with hx
  · exact div_nonneg (hg _) hx.le
  · exact nullPrefixDensity_nonneg y

theorem integral_productConditionalDensity {X : Type*} [MeasurableSpace X]
    (g : X × ℝ → ℝ) (x : X) : (∫ y, productConditionalDensity g x y) = 1 := by
  classical
  by_cases hx : 0 < productDensityMarginal g x
  · simp only [productConditionalDensity, if_pos hx]
    rw [integral_div]
    exact div_self hx.ne'
  · simp only [productConditionalDensity, if_neg hx]
    exact integral_nullPrefixDensity

theorem productConditionalDensity_bounded_support {X : Type*} [MeasurableSpace X]
    {g : X × ℝ → ℝ} {C R : ℝ} (hC : ∀ x y, g (x, y) ≤ C)
    (hR : ∀ x y, R < |y| → g (x, y) = 0) (x : X) :
    ∃ C' R' : ℝ, 0 ≤ R' ∧ (∀ y, productConditionalDensity g x y ≤ C') ∧
      (∀ y, R' < |y| → productConditionalDensity g x y = 0) := by
  classical
  refine ⟨if 0 < productDensityMarginal g x then C / productDensityMarginal g x else 1,
    max R 1, le_trans zero_le_one (le_max_right _ _), ?_, ?_⟩
  · intro y
    by_cases hx : 0 < productDensityMarginal g x
    · simp only [productConditionalDensity, if_pos hx]
      exact div_le_div_of_nonneg_right (hC x y) hx.le
    · simp only [productConditionalDensity, if_neg hx]
      exact nullPrefixDensity_le_one y
  · intro y hy
    have hyR : R < |y| := lt_of_le_of_lt (le_max_left _ _) hy
    have hy1 : 1 < |y| := lt_of_le_of_lt (le_max_right _ _) hy
    unfold productConditionalDensity
    split_ifs
    · rw [hR x y hyR, zero_div]
    · exact nullPrefixDensity_zero hy1

/-- Real density measures evaluated on measurable sets. -/
theorem realDensityMeasure_apply {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f base)
    {S : Set X} (hS : MeasurableSet S) :
    realDensityMeasure base f S = ENNReal.ofReal (∫ x in S, f x ∂base) := by
  rw [realDensityMeasure, withDensity_apply _ hS]
  exact (ofReal_integral_eq_lintegral_ofReal hfi.integrableOn (Filter.Eventually.of_forall hf)).symm

/-- A genuine marginal density obtained by integration, proved on all
measurable sets using Fubini. -/
theorem productDensityMarginal_map_fst {X : Type*} [MeasurableSpace X]
    (base : Measure X) [SFinite base] (g : X × ℝ → ℝ)
    (_hgm : Measurable g) (hg : ∀ p, 0 ≤ g p) (hgi : Integrable g (base.prod volume)) :
    (realDensityMeasure (base.prod volume) g).map Prod.fst =
      realDensityMeasure base (productDensityMarginal g) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_fst hS]
  have hpre : Prod.fst ⁻¹' S = S ×ˢ (univ : Set ℝ) := by ext p; simp
  rw [hpre, realDensityMeasure_apply (base.prod volume) g hg hgi (hS.prod MeasurableSet.univ),
    realDensityMeasure_apply base (productDensityMarginal g)
      (fun x => integral_nonneg fun y => hg (x, y)) hgi.integral_prod_left hS]
  congr 1
  have hmeasure : (base.restrict S).prod (volume : Measure ℝ) =
      (base.prod volume).restrict (S ×ˢ (univ : Set ℝ)) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := base) (ν := (volume : Measure ℝ)) S univ)
  have hgs : Integrable g ((base.restrict S).prod (volume : Measure ℝ)) := by
    rw [hmeasure]
    exact hgi.integrableOn
  rw [← hmeasure, integral_prod g hgs]
  rfl

/-- The key weighted identity holds almost everywhere even on a zero
marginal, where the fallback density is used. -/
theorem productConditionalDensity_weighted_identity {X : Type*} [MeasurableSpace X]
    {g : X × ℝ → ℝ} (hg : ∀ p, 0 ≤ g p)
    (hslice : ∀ x, Integrable (fun y => g (x, y))) (x : X) :
    ∀ᵐ y, productDensityMarginal g x * productConditionalDensity g x y = g (x, y) := by
  classical
  by_cases hx : 0 < productDensityMarginal g x
  · exact Filter.Eventually.of_forall fun y => by
      simp only [productConditionalDensity, if_pos hx]
      field_simp
  · have hm0 : productDensityMarginal g x = 0 :=
      le_antisymm (le_of_not_gt hx) (integral_nonneg fun y => hg (x, y))
    have hzero : (fun y => g (x, y)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun y => hg (x, y)) (hslice x)).mp hm0
    filter_upwards [hzero] with y hy
    simp [hm0, hy]

/-- Actual disintegration of a product density, proved by Fubini and
change of density. The test function is arbitrary and integrable. -/
theorem productConditionalDensity_disintegrate {X : Type*} [MeasurableSpace X]
    (base : Measure X) [SFinite base] (g : X × ℝ → ℝ)
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p)
    (hslice : ∀ x, Integrable (fun y => g (x, y))) (q : X × ℝ → ℝ)
    (hq : Integrable q (realDensityMeasure (base.prod volume) g)) :
    Integrable (fun x => ∫ y, q (x, y)
      ∂realDensityMeasure volume (productConditionalDensity g x))
      (realDensityMeasure base (productDensityMarginal g)) ∧
    (∫ p, q p ∂realDensityMeasure (base.prod volume) g) =
      ∫ x, (∫ y, q (x, y) ∂realDensityMeasure volume (productConditionalDensity g x))
        ∂realDensityMeasure base (productDensityMarginal g) := by
  let innerIntegral : X → ℝ := fun x => ∫ y, q (x, y)
    ∂realDensityMeasure volume (productConditionalDensity g x)
  have hqm : Integrable (fun p => g p * q p) (base.prod volume) :=
    (integrable_realDensityMeasure_iff (base.prod volume) g q hgm hg).mp hq
  have hpoint (x : X) : productDensityMarginal g x * innerIntegral x =
      ∫ y, g (x, y) * q (x, y) := by
    rw [show innerIntegral x = ∫ y, productConditionalDensity g x y * q (x, y) from
      integral_realDensityMeasure volume (productConditionalDensity g x) (fun y => q (x, y))
        ((productConditionalDensity_measurable hgm).comp (measurable_const.prodMk measurable_id))
        (productConditionalDensity_nonneg hg x)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [productConditionalDensity_weighted_identity hg hslice x] with y hy
    rw [← mul_assoc, hy]
  have hm : ∀ x, 0 ≤ productDensityMarginal g x := fun x => integral_nonneg fun y => hg (x, y)
  have hinner : Integrable innerIntegral (realDensityMeasure base (productDensityMarginal g)) := by
    apply (integrable_realDensityMeasure_iff base (productDensityMarginal g) innerIntegral
      (productDensityMarginal_measurable hgm) hm).mpr
    apply hqm.integral_prod_left.congr
    exact Filter.Eventually.of_forall fun x => (hpoint x).symm
  constructor
  · exact hinner
  · rw [integral_realDensityMeasure (base.prod volume) g q hgm hg,
      integral_prod _ hqm,
      integral_realDensityMeasure base (productDensityMarginal g) innerIntegral
        (productDensityMarginal_measurable hgm) hm]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => (hpoint x).symm

end Tusnady
