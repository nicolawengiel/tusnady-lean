import Tusnady.HaarTensorPrimitive

/-!
# The cube L² measure and the actual closed-upper-box primitive

This proves the essential bridge from equality of L² representatives to
pointwise equality of their actual anchored primitives on the unit cube.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open scoped BigOperators

/-- The product half-open cube measure equals Lebesgue measure restricted
to the manuscript's closed unit cube. Coordinate boundary hyperplanes
have zero measure; the equality is proved, not assumed. -/
theorem cubeMeasure_eq_restrict_unit (d : ℕ) :
    cubeMeasure d = (volume : Measure (Tusnady.Point d)).restrict (Tusnady.UnitCube d) := by
  have hset : Tusnady.UnitCube d = Set.pi Set.univ (fun _ : Fin d => Icc (0:ℝ) 1) := by
    ext x
    simp only [Tusnady.UnitCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Icc]
  calc
    cubeMeasure d = Measure.pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Icc (0:ℝ) 1)) := by
      unfold cubeMeasure unitMeasure
      congr 1
      funext k
      exact restrict_Ico_eq_restrict_Icc
    _ = (volume : Measure (Tusnady.Point d)).restrict (Tusnady.UnitCube d) := by
      rw [hset, volume_pi, Measure.restrict_pi_pi]

lemma upperBox_subset_unit {d : ℕ} (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.upperBox p ⊆ Tusnady.UnitCube d := by
  intro x hx k
  have h := hx k (Set.mem_univ k)
  exact ⟨(hp k).1.trans h.1, h.2⟩

/-- Restricting either cube measure or full volume to a closed upper box
inside the unit cube gives the same actual measure. -/
theorem cubeMeasure_restrict_upperBox {d : ℕ} (p : Tusnady.Point d)
    (hp : p ∈ Tusnady.UnitCube d) :
    (cubeMeasure d).restrict (Tusnady.upperBox p) =
      (volume : Measure (Tusnady.Point d)).restrict (Tusnady.upperBox p) := by
  rw [cubeMeasure_eq_restrict_unit]
  exact Measure.restrict_restrict_of_subset (upperBox_subset_unit p hp)

/-- The anchored primitive can be evaluated using the same measure as L². -/
theorem boxPrimitive_eq_integral_cubeMeasure {d : ℕ} (f : Tusnady.Point d → ℝ)
    (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive f p = ∫ x in Tusnady.upperBox p, f x ∂cubeMeasure d := by
  unfold Tusnady.boxPrimitive
  rw [cubeMeasure_restrict_upperBox p hp]

/-- Equality in cube L² yields equality of actual primitives at **every**
point of the unit cube, not just almost everywhere in the primitive variable. -/
theorem boxPrimitive_congr_cube_ae {d : ℕ} (f g : Tusnady.Point d → ℝ)
    (hfg : f =ᵐ[cubeMeasure d] g) (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive f p = Tusnady.boxPrimitive g p := by
  rw [boxPrimitive_eq_integral_cubeMeasure f p hp, boxPrimitive_eq_integral_cubeMeasure g p hp]
  exact integral_congr_ae (ae_restrict_of_ae hfg)

/-- The actual L² tensor vectors and their concrete real representatives
have the same anchored primitive at every valid point. -/
theorem boxPrimitive_tensorL2 {d H : ℕ} (label : TensorLabel d H)
    (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive (tensorL2 label) p = normalizedTensorPrimitiveValue label p := by
  rw [boxPrimitive_congr_cube_ae (tensorL2 label) (normalizedTensorValue label)
    (tensorL2_ae label) p hp]
  exact boxPrimitive_normalizedTensorValue label p (fun k => (hp k).2)

/-- The L² cube measure is supported on the manuscript's actual closed cube. -/
theorem cubeMeasure_ae_UnitCube (d : ℕ) :
    ∀ᵐ x ∂cubeMeasure d, x ∈ Tusnady.UnitCube d := by
  filter_upwards [cubeMeasure_ae_unit d] with x hx
  exact fun k => ⟨(hx k).1, (hx k).2.le⟩

end Tusnady.Haar
