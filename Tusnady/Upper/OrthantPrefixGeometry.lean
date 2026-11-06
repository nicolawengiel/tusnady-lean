import Tusnady.Upper.Statements
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Sorted last coordinates and orthant prefixes

Sorting uses mathlib's tie-aware tuple permutation.  A closed last-coordinate
threshold is exactly a prefix; equal coordinates are included together.  No
injectivity of coordinate projections or generic-position assumption is used.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Tusnady.Upper
attribute [local instance] Classical.propDecidable

/-- Delete the last coordinate of a point. -/
def frontPoint {s : ℕ} (x : Point (s + 1)) : Point s := fun j => x j.castSucc

/-- Sort by the last coordinate, with the original index breaking ties. -/
def lastSort {s N : ℕ} (P : Fin N → Point (s + 1)) : Equiv.Perm (Fin N) :=
  Tuple.sort (fun i => P i (Fin.last s))

theorem monotone_lastSort {s N : ℕ} (P : Fin N → Point (s + 1)) :
    Monotone (fun i => P (lastSort P i) (Fin.last s)) :=
  Tuple.monotone_sort (fun i => P i (Fin.last s))

/-- Number of sorted entries below a closed last-coordinate threshold. -/
def lastCut {s N : ℕ} (P : Fin N → Point (s + 1)) (x : Point (s + 1)) : Fin (N + 1) := by
  classical
  refine ⟨Fintype.card {i : Fin N // P (lastSort P i) (Fin.last s) ≤ x (Fin.last s)}, ?_⟩
  exact Nat.lt_succ_of_le (by simpa using (Fintype.card_subtype_le
    (fun i : Fin N => P (lastSort P i) (Fin.last s) ≤ x (Fin.last s))))

theorem last_le_iff_lt_lastCut {s N : ℕ} (P : Fin N → Point (s + 1))
    (x : Point (s + 1)) (i : Fin N) :
    P (lastSort P i) (Fin.last s) ≤ x (Fin.last s) ↔ (i : ℕ) < lastCut P x := by
  classical
  simpa [lastCut, Fintype.card_subtype] using (Tuple.lt_card_le_iff_apply_le_of_monotone
    (j := i) (f := fun i => P (lastSort P i) (Fin.last s))
    (a := x (Fin.last s)) (monotone_lastSort P)).symm

theorem anchored_iff_front_and_last {s : ℕ} (p x : Point (s + 1)) :
    p ∈ Anchored x ↔ frontPoint p ∈ Anchored (frontPoint x) ∧
      p (Fin.last s) ≤ x (Fin.last s) := by
  constructor
  · intro h
    exact ⟨fun j => h j.castSucc, h (Fin.last s)⟩
  · rintro ⟨hf, hl⟩ j
    exact Fin.lastCases hl (fun j => hf j) j

/-- Each sorted full orthant is a projected orthant intersected with one prefix. -/
theorem sorted_anchored_iff {s N : ℕ} (P : Fin N → Point (s + 1))
    (x : Point (s + 1)) (i : Fin N) :
    P (lastSort P i) ∈ Anchored x ↔
      frontPoint (P (lastSort P i)) ∈ Anchored (frontPoint x) ∧
        (i : ℕ) < lastCut P x := by
  rw [anchored_iff_front_and_last, last_le_iff_lt_lastCut]

/-- Real orthant sums can be written without an explicitly filtered finset. -/
theorem realAnchoredCount_eq_sum_ite {ι : Type*} [Fintype ι] {d : ℕ}
    (P : ι → Point d) (χ : ι → ℝ) (x : Point d) :
    realAnchoredCount P χ x = ∑ i, if P i ∈ Anchored x then χ i else 0 := by
  classical
  simp [realAnchoredCount, trace, Finset.sum_filter]

/-- Transporting a coloring back by a permutation preserves every original sum. -/
theorem realAnchoredCount_reindex {N d : ℕ} (P : Fin N → Point d)
    (σ : Equiv.Perm (Fin N)) (χ : Fin N → ℝ) (x : Point d) :
    realAnchoredCount P (fun i => χ (σ.symm i)) x =
      realAnchoredCount (fun i => P (σ i)) χ x := by
  classical
  simp only [realAnchoredCount_eq_sum_ite]
  simpa using (Equiv.sum_comp σ (fun i => if P i ∈ Anchored x then χ (σ.symm i) else 0)).symm

/-- A single coloring for the sorted points transports to a single coloring
for all original orthants. -/
theorem coloring_bound_of_reindex {N d : ℕ} (P : Fin N → Point d)
    (σ : Equiv.Perm (Fin N)) (χ : Fin N → ℝ) (hχ : IsSignColoring χ)
    (B : ℝ) (hbound : ∀ x, |realAnchoredCount (fun i => P (σ i)) χ x| ≤ B) :
    ∃ ψ : Fin N → ℝ, IsSignColoring ψ ∧ ∀ x, |realAnchoredCount P ψ x| ≤ B := by
  refine ⟨fun i => χ (σ.symm i), fun i => hχ _, ?_⟩
  intro x
  rw [realAnchoredCount_reindex]
  exact hbound x

end Tusnady.Upper
