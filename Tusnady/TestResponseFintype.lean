import Tusnady.TestResponse
import Tusnady.FiniteReindex

/-! Actual sampled-response duality for arbitrary finite coordinate labels,
in particular the manuscript's actual shell boxes. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open MeasureTheory Set
namespace Tusnady.Witness
variable {d h n : ℕ} {α : Type*} [Fintype α]

def sampledResponseFintype (P : Fin n → Point d) (B : Matrix (Fin n) α ℝ)
    (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun k => ∑ i, B i k * boxPrimitive (testFunction j theta u) (P i))

lemma inner_sampledResponseFintype (P : Fin n → Point d) (B : Matrix (Fin n) α ℝ)
    (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) (z : α → ℝ) :
    inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ α) (sampledResponseFintype P B j theta u) =
      ∑ i, B.mulVec z i * boxPrimitive (testFunction j theta u) (P i) := by
  unfold sampledResponseFintype
  rw [EuclideanSpace.inner_toLp_toLp]
  change (∑ k, (∑ i, B i k * boxPrimitive (testFunction j theta u) (P i))*z k) = _
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma continuous_sampledResponseFintype (P : Fin n → Point d) (hP : ∀ i, P i ∈ UnitCube d)
    (B : Matrix (Fin n) α ℝ) (j : Fin d) (theta : ℝ) :
    Continuous (sampledResponseFintype (h := h) P B j theta) := by
  apply (PiLp.continuous_toLp 2 (fun _ : α => ℝ)).comp
  apply continuous_pi
  intro k
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul (continuous_primitive_coefficients j theta (P i) (hP i))

/-- No dimension-of-coordinate-enumeration convention enters actual duality. -/
theorem sampledResponseFintype_duality {q : ℕ} (P : Fin n → Point (q+1))
    (hP : ∀ i, P i ∈ UnitCube (q+1)) (B : Matrix (Fin n) α ℝ)
    (j : Fin (q+1)) (theta : ℝ) (u : Shell (q+1) h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (z : α → ℝ) (t : ℝ) (ht : 0≤t)
    (hz : ∀ x ∈ UnitCube (q+1), |∑ i ∈ trace P x, B.mulVec z i| ≤ t) :
    inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ α) (sampledResponseFintype P B j theta u) ≤ t := by
  rw [inner_sampledResponseFintype]
  exact (le_abs_self _).trans (testFunction_weighted_duality j theta u hu P hP _ t ht hz)

end Tusnady.Witness
