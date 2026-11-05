import Tusnady.HaarFunctions

/-! # Actual Haar integrals and tent primitives. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators

lemma continuous_indicator_integrable (l u : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable ((Ico l u).indicator f) := by
  rw [integrable_indicator_iff measurableSet_Ico]
  exact hf.integrableOn_Icc.mono_set Ico_subset_Icc_self

lemma integral_indicator_interval (l u : ℝ) (hlu : l ≤ u) (f : ℝ → ℝ) :
    (∫ x, (Ico l u).indicator f x) = ∫ x in l..u, f x := by
  rw [integral_indicator measurableSet_Ico, ← integral_Icc_eq_integral_Ico,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hlu]

lemma integral_indicator_const_right (l u p s : ℝ) (hu : u ≤ 1) (hp : p ≤ 1) :
    (∫ x in p..1, (Ico l u).indicator (fun _ => s) x) =
      max (u-max l p) 0*s := by
  rw [intervalIntegral.integral_of_le hp, ← integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ico, integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico, Ico_inter_Ico]
  change (∫ _x in Ico (max l p) (min u 1), s) = _
  rw [min_eq_left hu, integral_const]
  simp only [Measure.restrict_apply_univ, smul_eq_mul, measureReal_def, Real.volume_Ico,
    ENNReal.toReal_ofReal']

lemma hBase_integrable : Integrable hBase :=
  (continuous_indicator_integrable 0 ((2:ℝ)⁻¹) _ continuous_const).sub
    (continuous_indicator_integrable ((2:ℝ)⁻¹) 1 _ continuous_const)

/-- The standard base tent, zero outside the real unit interval. -/
def tentBase (x : ℝ) : ℝ :=
  (Ico (0:ℝ) (2:ℝ)⁻¹).indicator (fun x => x) x +
    (Ico (2:ℝ)⁻¹ 1).indicator (fun x => 1-x) x

lemma tentBase_zero_outside (x : ℝ) (hx : x ∉ Ico (0:ℝ) 1) : tentBase x = 0 := by
  have hl : x ∉ Ico (0:ℝ) (2:ℝ)⁻¹ := by intro h; apply hx; constructor <;> norm_num at * <;> linarith [h.1, h.2]
  have hr : x ∉ Ico (2:ℝ)⁻¹ 1 := by intro h; apply hx; constructor <;> norm_num at * <;> linarith [h.1, h.2]
  simp only [tentBase, Set.indicator_of_notMem hl, Set.indicator_of_notMem hr, add_zero]

lemma tentBase_nonneg (x : ℝ) : 0 ≤ tentBase x := by
  unfold tentBase
  apply add_nonneg
  · apply Set.indicator_nonneg
    intro y hy
    exact hy.1
  · apply Set.indicator_nonneg
    intro y hy
    linarith [hy.2]

lemma hBase_primitive_formula (p : ℝ) (hp : p ≤ 1) :
    (∫ x in p..1, hBase x) =
      max ((2:ℝ)⁻¹-max 0 p) 0 - max (1-max (2:ℝ)⁻¹ p) 0 := by
  unfold hBase
  rw [intervalIntegral.integral_sub]
  · rw [integral_indicator_const_right _ _ _ _ (by norm_num) hp,
      integral_indicator_const_right _ _ _ _ le_rfl hp]
    ring
  · exact (continuous_indicator_integrable _ _ _ continuous_const).intervalIntegrable
  · exact (continuous_indicator_integrable _ _ _ continuous_const).intervalIntegrable

/-- The right primitive is exactly the negative tent at all real points. -/
theorem integral_hBase_right (p : ℝ) : (∫ x in p..1, hBase x) = -tentBase p := by
  by_cases hp0 : p < 0
  · have hout : p ∉ Ico (0:ℝ) 1 := fun h => (not_le_of_gt hp0) h.1
    rw [tentBase_zero_outside p hout, hBase_primitive_formula p (by linarith)]
    rw [max_eq_left hp0.le, max_eq_left (by norm_num; linarith : p ≤ (2:ℝ)⁻¹)]
    norm_num
  · have hpge : 0 ≤ p := le_of_not_gt hp0
    by_cases hph : p < (2:ℝ)⁻¹
    · have hl : p ∈ Ico (0:ℝ) (2:ℝ)⁻¹ := ⟨hpge, hph⟩
      have hr : p ∉ Ico (2:ℝ)⁻¹ 1 := fun h => (not_le_of_gt hph) h.1
      rw [hBase_primitive_formula p (by norm_num at hph; linarith), tentBase,
        Set.indicator_of_mem hl, Set.indicator_of_notMem hr,
        max_eq_right hpge, max_eq_left (sub_nonneg.mpr hph.le),
        max_eq_left hph.le]
      norm_num
    · have hpgh : (2:ℝ)⁻¹ ≤ p := le_of_not_gt hph
      by_cases hp1 : p < 1
      · have hl : p ∉ Ico (0:ℝ) (2:ℝ)⁻¹ := fun h => hph h.2
        have hr : p ∈ Ico (2:ℝ)⁻¹ 1 := ⟨hpgh, hp1⟩
        rw [hBase_primitive_formula p hp1.le, tentBase,
          Set.indicator_of_notMem hl, Set.indicator_of_mem hr,
          max_eq_right hpge, max_eq_right (sub_nonpos.mpr hpgh),
          max_eq_right hpgh, max_eq_left (sub_nonneg.mpr hp1.le)]
        ring
      · have hpge1 : 1 ≤ p := le_of_not_gt hp1
        have hout : p ∉ Ico (0:ℝ) 1 := fun h => hp1 h.2
        rw [tentBase_zero_outside p hout]
        calc
          (∫ x in p..1, hBase x) = ∫ _x in p..1, (0:ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_ge hpge1] at hx
            exact hBase_zero_outside x (fun h => (not_lt_of_ge hx.1) h.2)
          _ = -0 := by simp

/-- The Haar function has mean zero. -/
theorem integral_hBase : (∫ x, hBase x) = 0 := by
  unfold hBase
  rw [integral_sub (continuous_indicator_integrable _ _ _ continuous_const)
    (continuous_indicator_integrable _ _ _ continuous_const),
    integral_indicator_interval _ _ (by norm_num), integral_indicator_interval _ _ (by norm_num)]
  norm_num

lemma square_two_indicators (s t : Set ℝ) (hst : Disjoint s t) (f g : ℝ → ℝ) (x : ℝ) :
    (s.indicator f x+t.indicator g x)^2 =
      s.indicator (fun y => f y^2) x+t.indicator (fun y => g y^2) x := by
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t
  · exact False.elim ((Set.disjoint_left.mp hst) hs ht)
  all_goals simp [hs, ht]

/-- Actual integral of the squared base tent. -/
theorem integral_tentBase_sq : (∫ x, tentBase x^2) = (1:ℝ)/12 := by
  have hdisj : Disjoint (Ico (0:ℝ) (2:ℝ)⁻¹) (Ico (2:ℝ)⁻¹ 1) := by
    rw [Set.disjoint_left]
    intro x hx hy
    exact (not_lt_of_ge hy.1) hx.2
  have hfun : (fun x => tentBase x^2) = (fun x =>
      (Ico (0:ℝ) (2:ℝ)⁻¹).indicator (fun y => y^2) x +
        (Ico (2:ℝ)⁻¹ 1).indicator (fun y => (1-y)^2) x) := by
    funext x
    exact square_two_indicators _ _ hdisj (fun y => y) (fun y => 1-y) x
  have h₁ := continuous_indicator_integrable (0:ℝ) (2:ℝ)⁻¹ (fun y => y^2) (by fun_prop)
  have h₂ := continuous_indicator_integrable (2:ℝ)⁻¹ 1 (fun y => (1-y)^2) (by fun_prop)
  rw [hfun, integral_add h₁ h₂, integral_indicator_interval _ _ (by norm_num),
    integral_indicator_interval _ _ (by norm_num)]
  have hf₁ : (fun x : ℝ => x^2) = (fun x => ((1:ℝ)*x+0)^2) := by funext x; ring
  have hf₂ : (fun x : ℝ => (1-x)^2) = (fun x => ((-1:ℝ)*x+1)^2) := by funext x; ring
  rw [hf₁, hf₂, integral_affine_sq, integral_affine_sq]
  norm_num

/-- Standard nonnegative tent on a concrete dyadic interval. -/
def tentI (a : ℕ) (i : Fin (2^a)) (p : ℝ) : ℝ :=
  dyadicLength a * tentBase ((p-dyadicLeft a i)/dyadicLength a)

lemma hI_zero_outside (a : ℕ) (i : Fin (2^a)) (x : ℝ)
    (hx : x ∉ dyadicInterval a i) : hI a i x = 0 := by
  rw [hI_eq_hBase]
  exact hBase_zero_outside _ (fun h => hx ((normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).1 h))

lemma tentI_zero_outside (a : ℕ) (i : Fin (2^a)) (x : ℝ)
    (hx : x ∉ dyadicInterval a i) : tentI a i x = 0 := by
  unfold tentI
  rw [tentBase_zero_outside _ (fun h => hx ((normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).1 h)), mul_zero]

lemma hI_integrable (a : ℕ) (i : Fin (2^a)) : Integrable (hI a i) := by
  have hcomp := (hBase_integrable.comp_div (ne_of_gt (dyadicLength_pos a))).comp_sub_right (dyadicLeft a i)
  exact hcomp.congr (Filter.Eventually.of_forall (fun x => (hI_eq_hBase a i x).symm))

/-- Haar mean zero after actual affine change of variables. -/
theorem integral_hI (a : ℕ) (i : Fin (2^a)) : (∫ x, hI a i x) = 0 := by
  simp_rw [hI_eq_hBase]
  rw [integral_affine_pullback _ _ _ (dyadicLength_pos a), integral_hBase, mul_zero]

/-- Primitive of the actual Haar function, on its own interval. -/
theorem integral_hI_right_endpoint (a : ℕ) (i : Fin (2^a)) (p : ℝ) :
    (∫ x in p..dyadicLeft a i+dyadicLength a, hI a i x) = -tentI a i p := by
  have hl := ne_of_gt (dyadicLength_pos a)
  have hfun : (fun x => hI a i x) =
      (fun x => hBase (x/dyadicLength a-dyadicLeft a i/dyadicLength a)) := by
    funext x
    rw [hI_eq_hBase]
    congr 1
    ring
  rw [hfun, intervalIntegral.integral_comp_div_sub hBase hl]
  have hend : (dyadicLeft a i+dyadicLength a)/dyadicLength a-
      dyadicLeft a i/dyadicLength a = (1:ℝ) := by field_simp; ring
  rw [hend, integral_hBase_right]
  unfold tentI
  have harg : p/dyadicLength a-dyadicLeft a i/dyadicLength a =
      (p-dyadicLeft a i)/dyadicLength a := by ring
  rw [harg]
  simp only [smul_eq_mul]
  ring

/-- Exact primitive identity in the manuscript's unit-cube domain. -/
theorem integral_hI_right_unit (a : ℕ) (i : Fin (2^a)) (p : ℝ) :
    (∫ x in p..1, hI a i x) = -tentI a i p := by
  have hend : dyadicLeft a i+dyadicLength a ≤ (1:ℝ) := by
    have hi : (i.val:ℝ)+1 ≤ (2:ℝ)^a := by exact_mod_cast i.isLt
    unfold dyadicLeft dyadicLength
    have heq : (i.val:ℝ)/(2:ℝ)^a+1/(2:ℝ)^a = ((i.val:ℝ)+1)/(2:ℝ)^a := by ring
    rw [heq]
    apply (div_le_iff₀ (by positivity : (0:ℝ) < 2^a)).2
    simpa using hi
  have hzero : (∫ x in dyadicLeft a i+dyadicLength a..1, hI a i x) = 0 := by
    calc
      _ = ∫ _x in dyadicLeft a i+dyadicLength a..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hend] at hx
        exact hI_zero_outside a i x (fun h => (not_lt_of_ge hx.1) h.2)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    ((hI_integrable a i).intervalIntegrable (a := p) (b := dyadicLeft a i+dyadicLength a))
    ((hI_integrable a i).intervalIntegrable (a := dyadicLeft a i+dyadicLength a) (b := 1))
  rw [hzero, add_zero] at hsplit
  rw [← hsplit]
  exact integral_hI_right_endpoint a i p

/-- Exact squared L² mass of every real tent. -/
theorem integral_tentI_sq (a : ℕ) (i : Fin (2^a)) :
    (∫ x, tentI a i x^2) = dyadicLength a^3/12 := by
  have hfun : (fun x => tentI a i x^2) =
      (fun x => dyadicLength a^2 * (fun u => tentBase u^2)
        ((x-dyadicLeft a i)/dyadicLength a)) := by
    funext x
    unfold tentI
    ring
  rw [hfun, integral_const_mul,
    integral_affine_pullback (fun u => tentBase u^2) _ _ (dyadicLength_pos a), integral_tentBase_sq]
  ring

/-- Haar primitive norm, precisely the `|I|³/12` in Manuscript (2.4). -/
theorem integral_unit_haarPrimitive_sq (a : ℕ) (i : Fin (2^a)) :
    (∫ p in (0:ℝ)..1, (∫ x in p..1, hI a i x)^2) = dyadicLength a^3/12 := by
  simp_rw [integral_hI_right_unit, neg_sq]
  rw [integral_unit_eq_global]
  · exact integral_tentI_sq a i
  · intro x hx
    rw [tentI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h)), zero_pow (by omega)]

end Tusnady.Haar
