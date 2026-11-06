import Tusnady.PrekopaBrunnMinkowski1D
import Mathlib.MeasureTheory.Integral.Layercake

/-! Ball's normalized one-dimensional layer-cake argument. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace Tusnady.Prekopa

/-- The arithmetic-mean bound after separately normalizing both maxima to one.
All compactness and normalization premises are structural properties of the
functions; this theorem assumes no integral or correlation inequality. -/
theorem normalized_layercake_bound {f g h : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfmax : ∃ x, f x = 1) (hgmax : ∃ x, g x = 1)
    (hfc : ∀ t > 0, IsCompact {x | t ≤ f x})
    (hgc : ∀ t > 0, IsCompact {x | t ≤ g x})
    (hmid : ∀ x y, f x * g y ≤ (h ((x + y) / 2)) ^ 2) :
    ((∫ x, f x) + (∫ x, g x)) / 2 ≤ ∫ x, h x := by
  have hlev : ∀ t > 0,
      ENNReal.ofReal (1 / 2 : ℝ) *
        (volume {x | t ≤ f x} + volume {x | t ≤ g x}) ≤
        volume {x | t ≤ h x} := by
    intro t ht
    by_cases ht1 : t ≤ 1
    · obtain ⟨xf, hxf⟩ := hfmax
      obtain ⟨xg, hxg⟩ := hgmax
      apply compact_midpoint_measure_le (hfc t ht) (hgc t ht)
        ⟨xf, by simpa [hxf]⟩ ⟨xg, by simpa [hxg]⟩
      intro x hx y hy
      change t ≤ h ((x + y) / 2)
      have hm := hmid x y
      have hx0 := hf0 x
      have hy0 := hg0 y
      have hz0 := hh0 ((x + y) / 2)
      change t ≤ f x at hx
      change t ≤ g y at hy
      have hprod : t * t ≤ f x * g y := mul_le_mul hx hy ht.le hx0
      nlinarith
    · have hfe : {x | t ≤ f x} = ∅ := by
        ext x
        simp only [mem_setOf_eq, notMem_empty, iff_false]
        exact not_le.mpr ((hf1 x).trans_lt (lt_of_not_ge ht1))
      have hge : {x | t ≤ g x} = ∅ := by
        ext x
        simp only [mem_setOf_eq, notMem_empty, iff_false]
        exact not_le.mpr ((hg1 x).trans_lt (lt_of_not_ge ht1))
      simp [hfe, hge]
  have hmeas : Measurable (fun t : ℝ => volume {x | t ≤ f x}) := by
    apply Antitone.measurable
    intro a b hab
    exact measure_mono (fun x hx => hab.trans hx)
  have hlin := lintegral_mono_ae (μ := volume.restrict (Ioi (0 : ℝ)))
    (show ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ENNReal.ofReal (1 / 2 : ℝ) *
        (volume {x | t ≤ f x} + volume {x | t ≤ g x}) ≤
      volume {x | t ≤ h x} from by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hlev t ht)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_add_left hmeas,
    ← lintegral_eq_lintegral_meas_le volume (Eventually.of_forall hf0) hf.aemeasurable,
    ← lintegral_eq_lintegral_meas_le volume (Eventually.of_forall hg0) hg.aemeasurable,
    ← lintegral_eq_lintegral_meas_le volume (Eventually.of_forall hh0) hh.aemeasurable,
    ← ofReal_integral_eq_lintegral_ofReal hf (Eventually.of_forall hf0),
    ← ofReal_integral_eq_lintegral_ofReal hg (Eventually.of_forall hg0),
    ← ofReal_integral_eq_lintegral_ofReal hh (Eventually.of_forall hh0)] at hlin
  have hfint : 0 ≤ ∫ x, f x := integral_nonneg hf0
  have hgint : 0 ≤ ∫ x, g x := integral_nonneg hg0
  have hhint : 0 ≤ ∫ x, h x := integral_nonneg hh0
  rw [← ENNReal.ofReal_add hfint hgint, ← ENNReal.ofReal_mul (by norm_num)] at hlin
  apply (ENNReal.ofReal_le_ofReal_iff hhint).mp
  convert hlin using 1
  congr 1
  ring

end Tusnady.Prekopa

namespace Tusnady.Prekopa

/-- One-dimensional midpoint Prékopa–Leindler for nonnegative integrable
functions whose positive superlevel sets are compact and whose positive
maxima are attained. -/
theorem midpoint_integral_bound_of_compact_superlevels {f g h : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hfc : ∀ t > 0, IsCompact {x | t ≤ f x})
    (hgc : ∀ t > 0, IsCompact {x | t ≤ g x})
    (hfmax : ∃ xf, 0 < f xf ∧ ∀ x, f x ≤ f xf)
    (hgmax : ∃ xg, 0 < g xg ∧ ∀ x, g x ≤ g xg)
    (hmid : ∀ x y, f x * g y ≤ (h ((x + y) / 2)) ^ 2) :
    (∫ x, f x) * (∫ x, g x) ≤ (∫ x, h x) ^ 2 := by
  obtain ⟨xf, hA, hfA⟩ := hfmax
  obtain ⟨xg, hB, hgB⟩ := hgmax
  let A := f xf
  let B := g xg
  let c := Real.sqrt (A * B)
  have hAB : 0 < A * B := mul_pos hA hB
  have hc : 0 < c := Real.sqrt_pos.mpr hAB
  have hcsq : c ^ 2 = A * B := Real.sq_sqrt hAB.le
  have hnorm := normalized_layercake_bound
    (hf.div_const A) (hg.div_const B) (hh.div_const c)
    (fun x => div_nonneg (hf0 x) hA.le)
    (fun x => div_nonneg (hg0 x) hB.le)
    (fun x => div_nonneg (hh0 x) hc.le)
    (fun x => (div_le_one hA).mpr (hfA x))
    (fun x => (div_le_one hB).mpr (hgB x))
    ⟨xf, div_self hA.ne'⟩ ⟨xg, div_self hB.ne'⟩
    (fun t ht => by
      have heq : {x | t ≤ f x / A} = {x | t * A ≤ f x} := by
        ext x
        exact le_div_iff₀ hA
      rw [heq]
      exact hfc _ (mul_pos ht hA))
    (fun t ht => by
      have heq : {x | t ≤ g x / B} = {x | t * B ≤ g x} := by
        ext x
        exact le_div_iff₀ hB
      rw [heq]
      exact hgc _ (mul_pos ht hB))
    (fun x y => by
      have hm := div_le_div_of_nonneg_right (hmid x y) hAB.le
      convert hm using 1
      · field_simp
      · rw [div_pow, hcsq])
  simp only [integral_div] at hnorm
  have hfi : 0 ≤ (∫ x, f x) / A := div_nonneg (integral_nonneg hf0) hA.le
  have hgi : 0 ≤ (∫ x, g x) / B := div_nonneg (integral_nonneg hg0) hB.le
  have hhi : 0 ≤ (∫ x, h x) / c := div_nonneg (integral_nonneg hh0) hc.le
  have hprod : ((∫ x, f x) / A) * ((∫ x, g x) / B) ≤ ((∫ x, h x) / c) ^ 2 := by
    nlinarith [sq_nonneg ((∫ x, f x) / A - (∫ x, g x) / B)]
  have hquot : ((∫ x, f x) * (∫ x, g x)) / (A * B) ≤
      ((∫ x, h x) ^ 2) / (A * B) := by
    simpa only [div_mul_div_comm, div_pow, hcsq] using hprod
  exact (div_le_div_iff_of_pos_right hAB).mp hquot

end Tusnady.Prekopa
