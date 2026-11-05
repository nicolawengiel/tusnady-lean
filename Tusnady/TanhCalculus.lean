import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-! Concrete calculus bounds for the manuscript's smoothing function tanh. -/
namespace Tusnady

/-- A direct bound using the hyperbolic identity, with no tanh axiom. -/
theorem abs_tanh_lt_one (x : ℝ) : |Real.tanh x| < 1 := by
  have hc := Real.cosh_pos x
  have hid := Real.cosh_sq_sub_sinh_sq x
  have hs := abs_nonneg (Real.sinh x)
  have hsq := sq_abs (Real.sinh x)
  have habs : |Real.sinh x| < Real.cosh x := by nlinarith
  rw [Real.tanh_eq_sinh_div_cosh, abs_div, abs_of_pos hc]
  exact (div_lt_one hc).2 habs

theorem abs_tanh_le_one (x : ℝ) : |Real.tanh x| ≤ 1 := (abs_tanh_lt_one x).le

/-- The exact derivative in the bounded polynomial form used below. -/
theorem hasDerivAt_tanh (x : ℝ) :
    HasDerivAt Real.tanh (1 - Real.tanh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  convert h using 1
  · funext y
    exact Real.tanh_eq_sinh_div_cosh y
  · rw [Real.tanh_eq_sinh_div_cosh]
    field_simp

theorem tanh_derivative_bounds (x : ℝ) :
    0 ≤ 1 - Real.tanh x ^ 2 ∧ 1 - Real.tanh x ^ 2 ≤ 1 := by
  have ht := abs_tanh_le_one x
  have hsq := sq_abs (Real.tanh x)
  constructor <;> nlinarith [sq_nonneg (Real.tanh x), abs_nonneg (Real.tanh x)]

/-- Global Lipschitz control follows from the proved derivative formula. -/
theorem abs_tanh_sub_le (x y : ℝ) : |Real.tanh x - Real.tanh y| ≤ |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := Real.tanh) (s := Set.univ) (x := y) (y := x)
    (C := (1 : ℝ))
    (fun z _ => (hasDerivAt_tanh z).differentiableAt)
    (fun z _ => by
      rw [(hasDerivAt_tanh z).deriv, Real.norm_eq_abs,
        abs_of_nonneg (tanh_derivative_bounds z).1]
      exact (tanh_derivative_bounds z).2)
    convex_univ (Set.mem_univ _) (Set.mem_univ _)
  simpa only [Real.norm_eq_abs, one_mul] using h

theorem abs_tanh_le_abs (x : ℝ) : |Real.tanh x| ≤ |x| := by
  simpa using abs_tanh_sub_le x 0

/-- The lower derivative bound used for the first Walsh coefficient. -/
theorem tanh_derivative_lower (x : ℝ) :
    1 - x ^ 2 ≤ 1 - Real.tanh x ^ 2 := by
  have h := abs_tanh_le_abs x
  have hs := sq_abs (Real.tanh x)
  have hx := sq_abs x
  nlinarith [abs_nonneg x, abs_nonneg (Real.tanh x)]

noncomputable def tanhD₁ (x : ℝ) : ℝ := 1 - Real.tanh x ^ 2
noncomputable def tanhD₂ (x : ℝ) : ℝ := -2 * Real.tanh x * (1 - Real.tanh x ^ 2)
noncomputable def tanhD₃ (x : ℝ) : ℝ := (-2 + 6 * Real.tanh x ^ 2) * (1 - Real.tanh x ^ 2)

theorem hasDerivAt_tanhD₁ (x : ℝ) : HasDerivAt tanhD₁ (tanhD₂ x) x := by
  convert ((hasDerivAt_tanh x).pow 2).const_sub 1 using 1
  simp [tanhD₂]

theorem hasDerivAt_tanhD₂ (x : ℝ) : HasDerivAt tanhD₂ (tanhD₃ x) x := by
  have h := ((hasDerivAt_tanh x).mul (hasDerivAt_tanhD₁ x)).const_mul (-2)
  convert h using 1
  · funext y
    simp only [tanhD₂, tanhD₁, Pi.mul_apply]
    ring
  · simp only [tanhD₃, tanhD₂, tanhD₁]
    ring

/-- The exact uniform third derivative bound used in Lemma 2.3(iii). -/
theorem abs_tanhD₃_le_two (x : ℝ) : |tanhD₃ x| ≤ 2 := by
  have h0 : 0 ≤ Real.tanh x ^ 2 := sq_nonneg _
  have h1 : Real.tanh x ^ 2 ≤ 1 := by
    have h := (tanh_derivative_bounds x).1
    linarith
  have hp : 0 ≤ Real.tanh x ^ 2 * (1 - Real.tanh x ^ 2) :=
    mul_nonneg h0 (by linarith)
  unfold tanhD₃
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith [sq_nonneg (Real.tanh x ^ 2 - (2 : ℝ) / 3)]

end Tusnady
