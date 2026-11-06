import Tusnady.Upper.Ehrhard.ConvexConcavity
import Tusnady.Upper.Ehrhard.GaussianSections

/-!
# Identifying partial smoothing with genuine Gaussian sections

The first coordinates carry the Gaussian noise; the last coordinate is the
fixed section height. The probability identity is proved by the actual
coordinate marginal law, rather than supplied as a Gaussian hypothesis.
-/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace OAI.GaussianPropeller.GaussianSections
open EhrhardSmooth
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k+1))

/-- The actual continuous linear coordinate decomposition. -/
def splitEquiv : E' ≃L[ℝ] E × ℝ where
  toFun := split
  invFun := fun p => append p.1 p.2
  left_inv := append_front_last
  right_inv := by intro p; exact Prod.ext (front_append p.1 p.2) (append_last p.1 p.2)
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i
      rfl
    · rfl
  map_smul' := by
    intro a x
    apply Prod.ext
    · ext i
      rfl
    · rfl
  continuous_toFun := continuous_split
  continuous_invFun := continuous_append

def keepFront (i : Fin (k+1)) : Bool := decide (i ≠ Fin.last k)

lemma front_measurePreserving : MeasurePreserving (front : E' → E)
    (gaussianMeasure (Fin (k+1))) (gaussianMeasure (Fin k)) :=
  measurePreserving_fst.comp split_measurePreserving

lemma split_front_noise (z : E') (t : ℝ) :
    split (append (0 : E) t + CoordinateProjection.projection keepFront z) = (front z, t) := by
  apply Prod.ext
  · ext i
    simp [split, front, CoordinateProjection.projection_apply, keepFront]
  · simp [split, last, CoordinateProjection.projection_apply, keepFront, append]

/-- Exact relation between the analytic partial-noise probability and a
horizontal section of a set in the ordinary product space. -/
theorem sectionProbability_front (K : Set (E × ℝ)) (hK : MeasurableSet K) (t : ℝ) :
    sectionProbability (splitEquiv ⁻¹' K) (CoordinateProjection.projection keepFront)
      (append (0 : E) t) = (gaussianMeasure (Fin k)).real {y : E | (y,t) ∈ K} := by
  have hm : MeasurableSet {y : E | (y,t) ∈ K} :=
    hK.preimage (continuous_id.prodMk continuous_const).measurable
  have heq : (fun z : E' => append (0 : E) t + CoordinateProjection.projection keepFront z) ⁻¹'
      (splitEquiv ⁻¹' K) = front ⁻¹' {y : E | (y,t) ∈ K} := by
    ext z
    change split (append (0 : E) t + CoordinateProjection.projection keepFront z) ∈ K ↔ _
    rw [split_front_noise]
    rfl
  unfold sectionProbability
  rw [heq, measureReal_def, ← Measure.map_apply continuous_front.measurable hm,
    front_measurePreserving.map_eq]
  rfl

end OAI.GaussianPropeller.GaussianSections
