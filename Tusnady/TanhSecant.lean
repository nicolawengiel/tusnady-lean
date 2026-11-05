import Tusnady.FiniteDifference
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact quadratic lower bound on the tanh secant used for linear response. -/
open MeasureTheory
namespace Tusnady

theorem continuous_tanh : Continuous Real.tanh :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_tanh x).continuousAt

theorem continuous_tanhD₁ : Continuous tanhD₁ :=
  continuous_const.sub (continuous_tanh.pow 2)

/-- Integrating the proved derivative lower bound gives the manuscript's
exact cubic correction, rather than a weaker unquantified approximation. -/
theorem centralDifference_tanh_lower {h : ℝ} (hh : 0 ≤ h) (s : ℝ) :
    h * (1 - s ^ 2 - h ^ 2 / 3) ≤ centralDifference Real.tanh h s := by
  have hab : s - h ≤ s + h := by linarith
  have hint : IntervalIntegrable tanhD₁ volume (s - h) (s + h) :=
    continuous_tanhD₁.intervalIntegrable _ _
  have hpoly : IntervalIntegrable (fun x : ℝ => 1 - x ^ 2) volume (s - h) (s + h) :=
    (continuous_const.sub (continuous_id.pow 2) :
      Continuous (fun x : ℝ => 1 - x ^ 2)).intervalIntegrable _ _
  have hlo := intervalIntegral.integral_mono_on hab hpoly hint
    (fun x _ => tanh_derivative_lower x)
  have hftc : (∫ x in (s - h)..(s + h), tanhD₁ x) =
      Real.tanh (s + h) - Real.tanh (s - h) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_tanh x) hint
  have hval : (∫ x in (s - h)..(s + h), (1 - x ^ 2 : ℝ)) =
      2 * h * (1 - s ^ 2 - h ^ 2 / 3) := by
    rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ))
      (g := fun x : ℝ => x ^ 2) intervalIntegrable_const
      ((continuous_id.pow 2).intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, integral_pow]
    norm_num
    ring
  rw [hftc, hval] at hlo
  unfold centralDifference
  linarith

end Tusnady
