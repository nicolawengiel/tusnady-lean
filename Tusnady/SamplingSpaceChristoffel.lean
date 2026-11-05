import Tusnady.SamplingSpaceEvaluation

/-!
# Concrete inverse-Christoffel bounds for the actual detail spaces

Main.pdf Lemma 5.1(a), with explicit absolute constants 1/14 and 4.
The polynomial is derived from actual evaluation kernels and real cell
coordinates; the bounds are not supplied as a free basis hypothesis.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace
open DyadicFunctions

lemma localCoordinate_eq (j : ℕ) (i : Fin (2 ^ j)) (x : ℝ) :
    localCoordinate j i x = (2 : ℝ) ^ j * x - i.val := by
  unfold localCoordinate dyadicLeft dyadicLength
  field_simp

/-- Actual parent/child local coordinates, with the parity recording the
left or right child. -/
theorem localCoordinate_parent (j : ℕ) (i : Fin (2 ^ (j + 1))) (x : ℝ) :
    localCoordinate j (Dyadic.ancestorIndex i j (Nat.le_succ j)) x =
      (localCoordinate (j + 1) i x + (i.val % 2 : ℕ)) / 2 := by
  have hparent : (Dyadic.ancestorIndex i j (Nat.le_succ j)).val = i.val / 2 := by
    simp [Dyadic.ancestorIndex]
  have hmod : (((i.val % 2 : ℕ) : ℝ)) + 2 * ((i.val / 2 : ℕ) : ℝ) = (i.val : ℝ) := by
    exact_mod_cast Nat.mod_add_div i.val 2
  rw [localCoordinate_eq, localCoordinate_eq, hparent]
  rw [show (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 from pow_succ _ _]
  nlinarith [hmod]

theorem detailChristoffel_left_child (j : ℕ) (i : Fin (2 ^ (j + 1))) (x : ℝ)
    (hx : x ∈ dyadicInterval (j + 1) i) (hleft : i.val % 2 = 0) :
    detailChristoffel (j + 1) x = (2 : ℝ) ^ j *
      (4 + 21 * localCoordinate (j + 1) i x ^ 2 - 18 * localCoordinate (j + 1) i x) := by
  have hp := dyadicInterval_subset_ancestor (Nat.le_succ j) i hx
  rw [detailChristoffel_succ, basisChristoffel_on_cell (j + 1) i x hx,
    basisChristoffel_on_cell j (Dyadic.ancestorIndex i j (Nat.le_succ j)) x hp,
    localCoordinate_parent, hleft, Nat.cast_zero, add_zero]
  rw [show (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 from pow_succ _ _]
  ring

theorem detailChristoffel_right_child (j : ℕ) (i : Fin (2 ^ (j + 1))) (x : ℝ)
    (hx : x ∈ dyadicInterval (j + 1) i) (hright : i.val % 2 = 1) :
    detailChristoffel (j + 1) x = (2 : ℝ) ^ j *
      (4 + 21 * (1 - localCoordinate (j + 1) i x) ^ 2 -
        18 * (1 - localCoordinate (j + 1) i x)) := by
  have hp := dyadicInterval_subset_ancestor (Nat.le_succ j) i hx
  rw [detailChristoffel_succ, basisChristoffel_on_cell (j + 1) i x hx,
    basisChristoffel_on_cell j (Dyadic.ancestorIndex i j (Nat.le_succ j)) x hp,
    localCoordinate_parent, hright, Nat.cast_one]
  rw [show (2 : ℝ) ^ (j + 1) = (2 : ℝ) ^ j * 2 from pow_succ _ _]
  ring

/-- The left/right cell alternatives give precisely the manuscript
polynomial at a genuine unit-cell coordinate. -/
theorem detailChristoffel_polynomial (j : ℕ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      detailChristoffel (j + 1) x = (2 : ℝ) ^ j * (4 + 21 * s ^ 2 - 18 * s) := by
  obtain ⟨i, hi, _⟩ := Haar.existsUnique_unit_interval (j + 1) x hx
  have hs := (localCoordinate_mem_iff (j + 1) i x).mpr hi
  have hmod := Nat.mod_lt i.val (by omega : 0 < 2)
  have hcases : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
  rcases hcases with h | h
  · exact ⟨localCoordinate (j + 1) i x, hs.1, hs.2.le, detailChristoffel_left_child j i x hi h⟩
  · refine ⟨1 - localCoordinate (j + 1) i x, ?_, ?_, detailChristoffel_right_child j i x hi h⟩ <;>
      linarith [hs.1, hs.2]

/-- Uniform inverse-Christoffel bounds for every genuine D_j, including
D₀=V₀. These constants are independent of j and the point. -/
theorem detailChristoffel_bounds (j : ℕ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    ((1 : ℝ) / 14) * 2 ^ j ≤ detailChristoffel j x ∧
      detailChristoffel j x ≤ 4 * (2 : ℝ) ^ j := by
  cases j with
  | zero =>
    rw [detailChristoffel_zero]
    have h := basisChristoffel_bounds 0 x hx
    norm_num at h ⊢
    exact ⟨by linarith [h.1], h.2⟩
  | succ j =>
    obtain ⟨s, hs0, hs1, heq⟩ := detailChristoffel_polynomial j x hx
    rw [heq, pow_succ]
    have hlo := mul_le_mul_of_nonneg_left (Dyadic.christoffel_polynomial_lower s)
      (by positivity : 0 ≤ (2 : ℝ) ^ j)
    have hhi := mul_le_mul_of_nonneg_left (Dyadic.christoffel_polynomial_upper s hs0 hs1)
      (by positivity : 0 ≤ (2 : ℝ) ^ j)
    constructor
    · nlinarith [hlo]
    · nlinarith [hhi, pow_pos (by norm_num : (0 : ℝ) < 2) j]

/-- The same bounds for the actual canonical orthonormal detail basis,
ready for tensor-product sampling constructions. -/
theorem detailBasis_square_sum_bounds (j : ℕ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    ((1 : ℝ) / 14) * 2 ^ j ≤ (∑ i, detailBasis j i x ^ 2) ∧
      (∑ i, detailBasis j i x ^ 2) ≤ 4 * (2 : ℝ) ^ j := by
  rw [← detailChristoffel_basis_sum]
  exact detailChristoffel_bounds j x hx

end Tusnady.SamplingSpace
