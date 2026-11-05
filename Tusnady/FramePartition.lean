import Tusnady.FramePartitionBounds
import Tusnady.FrameTightPartition

/-! Full LT Proposition 2.1: actual two-part partition of a non-tight frame,
using the proved tight MSS partition and the proved whitening construction. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Frame
open Set
open scoped BigOperators InnerProductSpace
variable {D M : ℕ}

/-- Both actual parts satisfy the LT lower/upper recurrences. There is no
partition-existence or whitening premise in the theorem's hypotheses. -/
theorem exists_partition_bounds (v : Fin M → Space D) (α β δ : ℝ)
    (hδ : 0 < δ) (hα : 100*δ ≤ α) (_hβα : α ≤ β)
    (hNorm : ∀ j, ‖v j‖^2 ≤ δ)
    (hEnergy : ∀ x, α*‖x‖^2 ≤ energy v Finset.univ x ∧
      energy v Finset.univ x ≤ β*‖x‖^2) :
    ∃ S : Finset (Fin M),
      (∀ x, lowerStep δ α*‖x‖^2 ≤ energy v S x ∧
        energy v S x ≤ upperStep δ α β*‖x‖^2) ∧
      (∀ x, lowerStep δ α*‖x‖^2 ≤ energy v (Finset.univ \ S) x ∧
        energy v (Finset.univ \ S) x ≤ upperStep δ α β*‖x‖^2) := by
  have ha : 0 < α := lt_of_lt_of_le (by positivity) hα
  obtain ⟨u,hu,hun,L,hE,hL⟩ := exists_whitening v α β δ ha
    (fun x => (hEnergy x).1) (fun x => (hEnergy x).2) hNorm
  obtain ⟨S,hS,hcomp⟩ := exists_tight_partition u hu (div_pos hδ ha) hun
  refine ⟨S,partition_transfer v u α β δ hδ hα hu L hE hL S ?_ ?_⟩
  · simpa only [partitionFactor] using hS
  · simpa only [partitionFactor] using hcomp

end Tusnady.Frame
