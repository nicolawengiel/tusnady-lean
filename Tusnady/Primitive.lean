import Tusnady.Definitions
import Mathlib.MeasureTheory.Integral.Pi

/-!
# The actual anchored-box primitive

This is J* from Main.pdf, as a genuine Lebesgue set integral on the closed
upper box. Product formulas are proved by the actual finite-product Fubini
theorem. Integrability is explicit whenever linearity requires it.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady

def upperBox (p : Point d) : Set (Point d) :=
  Set.pi Set.univ (fun j => Set.Icc (p j) (1 : ℝ))

def boxPrimitive (f : Point d → ℝ) (p : Point d) : ℝ :=
  ∫ x in upperBox p, f x

theorem upperBox_measurable (p : Point d) : MeasurableSet (upperBox p) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Icc)

/-- The closed upper-box integral is exactly the corresponding product
of restricted one-dimensional Lebesgue measures. -/
theorem boxPrimitive_eq_pi (f : Point d → ℝ) (p : Point d) :
    boxPrimitive f p = ∫ x, f x ∂Measure.pi (fun j =>
      (volume : Measure ℝ).restrict (Icc (p j) (1 : ℝ))) := by
  unfold boxPrimitive upperBox
  rw [volume_pi, Measure.restrict_pi_pi]

/-- Exact tensor-product primitive. -/
theorem boxPrimitive_tensor (f : Fin d → ℝ → ℝ) (p : Point d) :
    boxPrimitive (fun x => ∏ j, f j (x j)) p =
      ∏ j, ∫ x in Icc (p j) (1 : ℝ), f j x := by
  rw [boxPrimitive_eq_pi]
  exact integral_fintype_prod_eq_prod f

/-- Interval-primitive form on the manuscript's domain p_j≤1. -/
theorem boxPrimitive_tensor_interval (f : Fin d → ℝ → ℝ) (p : Point d)
    (hp : ∀ j, p j ≤ 1) :
    boxPrimitive (fun x => ∏ j, f j (x j)) p =
      ∏ j, ∫ x in (p j)..1, f j x := by
  rw [boxPrimitive_tensor]
  apply Finset.prod_congr rfl
  intro j _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hp j)]

theorem boxPrimitive_const_mul (c : ℝ) (f : Point d → ℝ) (p : Point d) :
    boxPrimitive (fun x => c * f x) p = c * boxPrimitive f p := by
  exact integral_const_mul c f

theorem boxPrimitive_add (f g : Point d → ℝ) (p : Point d)
    (hf : IntegrableOn f (upperBox p)) (hg : IntegrableOn g (upperBox p)) :
    boxPrimitive (fun x => f x + g x) p = boxPrimitive f p + boxPrimitive g p :=
  integral_add hf hg

theorem boxPrimitive_sum {α : Type*} (s : Finset α) (f : α → Point d → ℝ)
    (p : Point d) (hf : ∀ a ∈ s, IntegrableOn (f a) (upperBox p)) :
    boxPrimitive (fun x => ∑ a ∈ s, f a x) p = ∑ a ∈ s, boxPrimitive (f a) p :=
  integral_finset_sum s hf

end Tusnady
