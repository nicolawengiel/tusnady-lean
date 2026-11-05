import Tusnady.PrimitiveDuality
import Tusnady.CellAnalytic
import Tusnady.PointGaussianBody

/-!
# Actual sampled response and its discrepancy duality

The vector is the literal transposed-matrix response of the actual
primitive of W at the actual sample points. Its continuity and Gaussian-
body duality follow from the concrete W, not from abstract response inputs.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory Set
namespace Tusnady.Witness
variable {d h n M : ℕ}

/-- Actual B-transpose response of the sampled J*W. -/
def sampledTestResponse (P : Fin n → Point d) (B : Matrix (Fin n) (Fin M) ℝ)
    (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) : EuclideanSpace ℝ (Fin M) :=
  WithLp.toLp 2 (fun k => ∑ i, B i k * boxPrimitive (testFunction j theta u) (P i))

lemma inner_sampledTestResponse (P : Fin n → Point d) (B : Matrix (Fin n) (Fin M) ℝ)
    (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) (z : Fin M → ℝ) :
    inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin M)) (sampledTestResponse P B j theta u) =
      ∑ i, B.mulVec z i * boxPrimitive (testFunction j theta u) (P i) := by
  unfold sampledTestResponse
  rw [EuclideanSpace.inner_toLp_toLp]
  change (∑ k, (∑ i, B i k * boxPrimitive (testFunction j theta u) (P i))*z k) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ k, (B i k * boxPrimitive (testFunction j theta u) (P i))*z k) = _
  rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Continuity in every real coefficient vector, not just almost
surely under the later Rosenblatt law. -/
theorem continuous_sampledTestResponse (P : Fin n → Point d) (hP : ∀ i, P i ∈ UnitCube d)
    (B : Matrix (Fin n) (Fin M) ℝ) (j : Fin d) (theta : ℝ) :
    Continuous (sampledTestResponse (h := h) P B j theta) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin M => ℝ)).comp
  apply continuous_pi
  intro k
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (continuous_primitive_coefficients j theta (P i) (hP i))

/-- Actual duality on the actual Gaussian discrepancy body. -/
theorem sampledTestResponse_duality {q : ℕ} (P : Fin n → Point (q+1))
    (hP : ∀ i, P i ∈ OpenUnitCube (q+1)) (B : Matrix (Fin n) (Fin M) ℝ)
    (j : Fin (q+1)) (theta : ℝ) (u : Shell (q+1) h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (z : Fin M → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hz : z ∈ pointGaussianBody P B t) :
    inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin M)) (sampledTestResponse P B j theta u) ≤ t := by
  rw [inner_sampledTestResponse]
  apply le_trans (le_abs_self _)
  apply testFunction_weighted_duality j theta u hu P
    (fun i k => ⟨(hP i k).1.le, (hP i k).2.le⟩) _ t ht
  exact (mem_pointGaussianBody_iff_unitCube P hP B t z).mp hz

end Tusnady.Witness
