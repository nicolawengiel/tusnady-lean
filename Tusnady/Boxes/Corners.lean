import Tusnady.Boxes.Definitions

/-!
Unrestricted real corners. The existing `Tusnady.Box a b` is empty if a lower
corner exceeds an upper corner. This file shows that the valid-query API
controls every pair of corners, including these empty boxes.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Boxes
variable {ι : Type*} [Fintype ι] {d : ℕ}

def realCountCorners (P : ι → Point d) (χ : ι → ℝ) (a b : Point d) : ℝ := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => P i ∈ Tusnady.Box a b), χ i

@[simp] theorem realCountCorners_query (P : ι → Point d) (χ : ι → ℝ) (q : Query d) :
    realCountCorners P χ q.lower q.upper = realCount P χ q := rfl

theorem realCountCorners_eq_zero_of_invalid (P : ι → Point d) (χ : ι → ℝ)
    (a b : Point d) (h : ¬ ∀ j, a j ≤ b j) : realCountCorners P χ a b = 0 := by
  classical
  have hempty : Finset.univ.filter (fun i => P i ∈ Tusnady.Box a b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hp := (Finset.mem_filter.mp hi).2
    change ∀ j, a j ≤ P i j ∧ P i j ≤ b j at hp
    exact h (fun j => (hp j).1.trans (hp j).2)
  simp only [realCountCorners, hempty, Finset.sum_empty]

theorem abs_realCountCorners_le_of_queries (P : ι → Point d) (χ : ι → ℝ) (B : ℝ)
    (h : ∀ q : Query d, |realCount P χ q| ≤ B) (a b : Point d) :
    |realCountCorners P χ a b| ≤ B := by
  classical
  by_cases hab : ∀ j, a j ≤ b j
  · exact h ⟨a, b, hab⟩
  · rw [realCountCorners_eq_zero_of_invalid P χ a b hab, abs_zero]
    exact (abs_nonneg (realCount P χ (Query.zero d))).trans (h (Query.zero d))

theorem queries_bound_iff_corners_bound (P : ι → Point d) (χ : ι → ℝ) (B : ℝ) :
    (∀ q : Query d, |realCount P χ q| ≤ B) ↔
      ∀ a b : Point d, |realCountCorners P χ a b| ≤ B := by
  constructor
  · exact abs_realCountCorners_le_of_queries P χ B
  · intro h q
    exact h q.lower q.upper

end Tusnady.Boxes
