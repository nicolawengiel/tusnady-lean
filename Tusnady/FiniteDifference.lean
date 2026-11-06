import Tusnady.TanhCalculus
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Bounds for actual centered finite differences, using proved derivatives. -/
noncomputable section
namespace Tusnady

/-- A centered finite difference divided by two, matching cube derivatives. -/
def centralDifference (f : ℝ → ℝ) (h s : ℝ) : ℝ :=
  (f (s + h) - f (s - h)) / 2

def iterDifference (h : ℝ) : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => centralDifference (iterDifference h n f) h

/-- Differentiation commutes with an actual centered finite difference. -/
theorem hasDerivAt_centralDifference {f f' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) (h s : ℝ) :
    HasDerivAt (centralDifference f h) (centralDifference f' h s) s := by
  have hp := HasDerivAt.comp_add_const s h (hf (s + h))
  have hm := HasDerivAt.comp_sub_const s h (hf (s - h))
  convert! (hp.sub hm).div_const 2 using 1 <;> rfl

/-- The integral-free mean-value bound needed for the third discrete
Walsh derivative. No existence of a third-order MVT point is assumed. -/
theorem abs_centralDifference_le {f f' : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (f' s) s) {C : ℝ}
    (hbound : ∀ s, |f' s| ≤ C) (h s : ℝ) :
    |centralDifference f h s| ≤ C * |h| := by
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := Set.univ) (x := s - h) (y := s + h)
    (fun t _ => (hf t).hasDerivWithinAt)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hbound t)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  have heq : s + h - (s - h) = 2 * h := by ring
  simp only [Real.norm_eq_abs, heq, abs_mul] at hm
  norm_num at hm
  unfold centralDifference
  rw [abs_div]
  norm_num
  linarith

/-- Three successive differences are controlled by an actual third
continuous derivative with the exact step factor |h|³. -/
theorem abs_iterDifference_three_le {f f₁ f₂ f₃ : ℝ → ℝ}
    (h₀ : ∀ s, HasDerivAt f (f₁ s) s)
    (h₁ : ∀ s, HasDerivAt f₁ (f₂ s) s)
    (h₂ : ∀ s, HasDerivAt f₂ (f₃ s) s)
    {C : ℝ} (hbound : ∀ s, |f₃ s| ≤ C) (h s : ℝ) :
    |iterDifference h 3 f s| ≤ C * |h| ^ 3 := by
  have hb₁ (s : ℝ) : |centralDifference f₂ h s| ≤ C * |h| :=
    abs_centralDifference_le h₂ hbound h s
  have hd₁ (s : ℝ) : HasDerivAt (centralDifference f₁ h)
      (centralDifference f₂ h s) s := hasDerivAt_centralDifference h₁ h s
  have hb₂ (s : ℝ) : |centralDifference (centralDifference f₁ h) h s| ≤
      (C * |h|) * |h| := abs_centralDifference_le hd₁ hb₁ h s
  have hd₀ (s : ℝ) : HasDerivAt (centralDifference f h)
      (centralDifference f₁ h s) s := hasDerivAt_centralDifference h₀ h s
  have hd₀' (s : ℝ) : HasDerivAt (centralDifference (centralDifference f h) h)
      (centralDifference (centralDifference f₁ h) h s) s :=
    hasDerivAt_centralDifference hd₀ h s
  have hfinal := abs_centralDifference_le hd₀' hb₂ h s
  simpa only [iterDifference, pow_succ, pow_zero, mul_one, one_mul, mul_assoc] using hfinal

theorem abs_tanh_third_difference {theta : ℝ} (htheta : 0 ≤ theta) (s : ℝ) :
    |iterDifference theta 3 Real.tanh s| ≤ 2 * theta ^ 3 := by
  simpa only [abs_of_nonneg htheta] using
    abs_iterDifference_three_le hasDerivAt_tanh hasDerivAt_tanhD₁ hasDerivAt_tanhD₂
      abs_tanhD₃_le_two theta s

end Tusnady
