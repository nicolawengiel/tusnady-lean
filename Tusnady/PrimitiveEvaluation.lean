import Tusnady.PrimitiveL2

/-! # Actual bounded point evaluation of the anchored primitive

This evaluates the integral kernel, never an arbitrary L² representative
at a point. Its bound is uniform in the evaluation point.
-/

noncomputable section
open MeasureTheory
namespace Tusnady.Haar

def pointPrimitiveLinear (d : ℕ) (p : Point d) : Lp ℝ 2 (cubeMeasure d) →ₗ[ℝ] ℝ where
  toFun f := primitiveRepresentative f p
  map_add' f g := primitiveRepresentative_add f g p
  map_smul' c f := by
    simpa only [RingHom.id_apply, smul_eq_mul] using primitiveRepresentative_smul c f p

def pointPrimitiveCLM (d : ℕ) (p : Point d) : Lp ℝ 2 (cubeMeasure d) →L[ℝ] ℝ :=
  (pointPrimitiveLinear d p).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using primitiveRepresentative_norm_le f p)

theorem pointPrimitiveCLM_eq_boxPrimitive (d : ℕ) (p : Point d) (hp : p ∈ UnitCube d)
    (f : Lp ℝ 2 (cubeMeasure d)) : pointPrimitiveCLM d p f = boxPrimitive f p := by
  exact (boxPrimitive_eq_integral_cubeMeasure f p hp).symm

def pointPrimitiveHighCLM (d H h : ℕ) (p : Point d) : Lp ℝ 2 (cubeMeasure d) →L[ℝ] ℝ :=
  (pointPrimitiveCLM d p).comp (highProjectionCLM d H h)

theorem pointPrimitiveHighCLM_eq_boxPrimitive (d H h : ℕ) (p : Point d) (hp : p ∈ UnitCube d)
    (f : Lp ℝ 2 (cubeMeasure d)) :
    pointPrimitiveHighCLM d H h p f = boxPrimitive (highProjection d H h f) p :=
  pointPrimitiveCLM_eq_boxPrimitive d p hp (highProjection d H h f)

end Tusnady.Haar
