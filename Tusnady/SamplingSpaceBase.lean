import Tusnady.DyadicFunctionsGeometry
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Actual local affine sampling functions

All functions are pointwise real functions with explicit half-open support.
Their inner products below are actual Lebesgue Bochner integrals.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

/-- Zero extension of a function from the half-open unit interval. -/
def unitPatch (f : ℝ → ℝ) : ℝ → ℝ := (Ico (0 : ℝ) 1).indicator f

lemma unitPatch_integrable (f : ℝ → ℝ) (hf : Continuous f) : Integrable (unitPatch f) := by
  unfold unitPatch
  rw [integrable_indicator_iff measurableSet_Ico]
  exact hf.integrableOn_Icc.mono_set Ico_subset_Icc_self

lemma integral_unitPatch (f : ℝ → ℝ) :
    (∫ x, unitPatch f x) = ∫ x in (0 : ℝ)..1, f x := by
  rw [unitPatch, integral_indicator measurableSet_Ico, ← integral_Icc_eq_integral_Ico,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

lemma unitPatch_mul (f g : ℝ → ℝ) (x : ℝ) :
    unitPatch f x * unitPatch g x = unitPatch (fun t => f t * g t) x := by
  by_cases hx : x ∈ Ico (0 : ℝ) 1 <;> simp [unitPatch, hx]

/-- A single quadratic integral calculation suffices for all affine basis
mixed products; no orthogonality fact is assumed. -/
theorem integral_unitPatch_quadratic (a b c : ℝ) :
    (∫ x, unitPatch (fun x => a * x ^ 2 + b * x + c) x) = a / 3 + b / 2 + c := by
  rw [integral_unitPatch]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul b (fun x : ℝ => x), integral_id]
  simp only [intervalIntegral.integral_const_mul, integral_pow,
    intervalIntegral.integral_const, sub_zero, one_pow, one_smul]
  norm_num
  ring

/-- The two affine modes on the reference interval: constant and centered
linear Legendre mode, with their actual normalizing constant. -/
def affineMode (b : Bool) (x : ℝ) : ℝ :=
  if b then Real.sqrt 3 * (2 * x - 1) else 1

def baseBasis (b : Bool) : ℝ → ℝ := unitPatch (affineMode b)

lemma affineMode_continuous (b : Bool) : Continuous (affineMode b) := by
  cases b <;> unfold affineMode <;> dsimp <;> fun_prop

lemma baseBasis_zero_outside (b : Bool) (x : ℝ) (hx : x ∉ Ico (0 : ℝ) 1) :
    baseBasis b x = 0 := by simp [baseBasis, unitPatch, hx]

/-- Genuine orthonormality on the unit interval, computed by integration. -/
theorem baseBasis_inner (b c : Bool) :
    (∫ x, baseBasis b x * baseBasis c x) = if b = c then 1 else 0 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  simp only [baseBasis, unitPatch_mul]
  cases b <;> cases c
  · simpa [affineMode] using integral_unitPatch_quadratic 0 0 1
  · have hp : (fun t => affineMode false t * affineMode true t) =
        (fun t => 0 * t ^ 2 + (2 * Real.sqrt 3) * t + (-Real.sqrt 3)) := by
      funext t
      simp [affineMode]
      ring
    rw [hp, integral_unitPatch_quadratic]
    norm_num
  · have hp : (fun t => affineMode true t * affineMode false t) =
        (fun t => 0 * t ^ 2 + (2 * Real.sqrt 3) * t + (-Real.sqrt 3)) := by
      funext t
      simp [affineMode]
      ring
    rw [hp, integral_unitPatch_quadratic]
    norm_num
  · have hp : (fun t => affineMode true t * affineMode true t) =
        (fun t => 12 * t ^ 2 + (-12) * t + 3) := by
      funext t
      simp only [affineMode, ↓reduceIte]
      calc
        _ = (Real.sqrt 3) ^ 2 * (2 * t - 1) ^ 2 := by ring
        _ = _ := by rw [hsqrt]; ring
    rw [hp, integral_unitPatch_quadratic]
    norm_num

lemma baseBasis_product_integrable (b c : Bool) :
    Integrable (fun x => baseBasis b x * baseBasis c x) := by
  simpa only [baseBasis, unitPatch_mul] using
    unitPatch_integrable (fun x => affineMode b x * affineMode c x)
      ((affineMode_continuous b).mul (affineMode_continuous c))

lemma baseBasis_memLp (b : Bool) : MemLp (baseBasis b) 2 (volume : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq ?_).mpr
  · simpa only [pow_two] using baseBasis_product_integrable b b
  · exact ((affineMode_continuous b).measurable.indicator measurableSet_Ico).aestronglyMeasurable

/-- Pointwise inverse-Christoffel value of the actual two-mode basis. -/
theorem baseBasis_christoffel (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    (∑ b : Bool, baseBasis b x ^ 2) = 1 + 12 * (x - 1 / 2) ^ 2 := by
  have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
  simp [baseBasis, unitPatch, hx, affineMode, mul_pow, hsqrt]
  ring

end Tusnady.SamplingSpace
