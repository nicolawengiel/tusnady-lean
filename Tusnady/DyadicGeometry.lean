import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Higher-dimensional shell shapes and joins

The combinatorial part of Manuscript §§3.1, 4.1, 4.3. Coordinates are actual
nonnegative depths, divisible by three. In particular `excess` is not an
independent parameter or an assumed estimate.

This module does not assert the analytic cell-location or remainder estimate.
-/

set_option autoImplicit false

namespace Tusnady.Dyadic

open scoped BigOperators

/-- A shell shape: the depth vector of a box of volume `2⁻ʰ`. -/
@[ext] structure Shape (d h : ℕ) where
  depth : Fin d → ℕ
  sum_depth : ∑ k, depth k = h
  three_dvd_depth : ∀ k, 3 ∣ depth k
  deriving DecidableEq

variable {d h : ℕ}

/-- Each side depth is bounded by the total shell depth. -/
theorem depth_le_shell (r : Shape d h) (k : Fin d) : r.depth k ≤ h := by
  calc
    r.depth k ≤ ∑ i, r.depth i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (r.depth i)) (Finset.mem_univ k)
    _ = h := r.sum_depth

/-- Distinct permitted depths differ by at least three. -/
theorem depth_separation (r s : Shape d h) (k : Fin d)
    (hlt : r.depth k < s.depth k) : r.depth k + 3 ≤ s.depth k := by
  obtain ⟨a, ha⟩ := r.three_dvd_depth k
  obtain ⟨b, hb⟩ := s.three_dvd_depth k
  omega

/-- Coordinatewise maximum, with zero for the empty family. -/
def join (S : Finset (Shape d h)) (k : Fin d) : ℕ :=
  S.sup (fun r => r.depth k)

/-- Total join depth. -/
def joinDepth (S : Finset (Shape d h)) : ℕ := ∑ k, join S k

/-- Excess of a join over the shell. The lower-bound theorem justifies this
natural-number subtraction for nonempty shape families. -/
def excess (S : Finset (Shape d h)) : ℕ := joinDepth S - h

/-- Every member is coordinatewise below its join. -/
theorem depth_le_join (S : Finset (Shape d h)) {r : Shape d h}
    (hr : r ∈ S) (k : Fin d) : r.depth k ≤ join S k := by
  exact Finset.le_sup (f := fun r : Shape d h => r.depth k) hr

/-- The join stays in the permitted depth lattice. -/
theorem three_dvd_join (S : Finset (Shape d h)) (k : Fin d) : 3 ∣ join S k := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨r, hr, heq⟩ := Finset.exists_mem_eq_sup S hS (fun r => r.depth k)
    change 3 ∣ S.sup (fun r => r.depth k)
    rw [heq]
    exact r.three_dvd_depth k
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [hEmpty, join]

/-- A nonempty join cannot have depth less than its members. -/
theorem shell_le_joinDepth (S : Finset (Shape d h)) (hS : S.Nonempty) :
    h ≤ joinDepth S := by
  obtain ⟨r, hr⟩ := hS
  calc
    h = ∑ k, r.depth k := r.sum_depth.symm
    _ ≤ joinDepth S := Finset.sum_le_sum (fun k _ => depth_le_join S hr k)

/-- Each join coordinate is at most the shell depth. -/
theorem join_le_shell (S : Finset (Shape d h)) (k : Fin d) : join S k ≤ h := by
  exact Finset.sup_le (fun r _ => depth_le_shell r k)

/-- The total join depth is at most dimension times shell depth. -/
theorem joinDepth_le (S : Finset (Shape d h)) : joinDepth S ≤ d * h := by
  calc
    joinDepth S ≤ ∑ _k : Fin d, h := Finset.sum_le_sum (fun k _ => join_le_shell S k)
    _ = d * h := by simp

/-- The defining excess identity, without truncated-subtraction ambiguity. -/
theorem excess_add_shell (S : Finset (Shape d h)) (hS : S.Nonempty) :
    excess S + h = joinDepth S := by
  exact Nat.sub_add_cancel (shell_le_joinDepth S hS)

/-- Manuscript §4.1: `0 ≤ e ≤ (d−1)h`. Nonnegativity is encoded by `ℕ`. -/
theorem excess_le (hd : 1 ≤ d) (S : Finset (Shape d h)) (hS : S.Nonempty) :
    excess S ≤ (d - 1) * h := by
  have hsum := excess_add_shell S hS
  have hupper := joinDepth_le S
  have hsplit : d * h = (d - 1) * h + h := by
    calc
      d * h = ((d - 1) + 1) * h := by rw [Nat.sub_add_cancel hd]
      _ = (d - 1) * h + h := by rw [Nat.add_mul, one_mul]
  omega

/-- Shapes below a prescribed join; the bound is part of the domain so that
natural subtraction can be canceled. -/
def ShapesBelow (j : Fin d → ℕ) := {r : Shape d h // ∀ k, r.depth k ≤ j k}

/-- The deficit encoding used in the counting argument. -/
def deficit (j : Fin d → ℕ) (r : ShapesBelow (h := h) j) : Fin d → ℕ :=
  fun k => j k - r.val.depth k

/-- No two shapes below the same join have the same deficit vector. -/
theorem deficit_injective (j : Fin d → ℕ) :
    Function.Injective (deficit (h := h) j) := by
  intro r s heq
  apply Subtype.ext
  apply Shape.ext
  funext k
  have hr := r.property k
  have hs := s.property k
  have hk := congrFun heq k
  change j k - r.val.depth k = j k - s.val.depth k at hk
  omega

/-- The sum of the deficits is exactly the excess, not merely bounded by it. -/
theorem sum_deficit (j : Fin d → ℕ) (r : ShapesBelow (h := h) j) :
    ∑ k, deficit j r k = (∑ k, j k) - h := by
  unfold deficit
  rw [Finset.sum_tsub_distrib Finset.univ (fun k _ => r.property k), r.val.sum_depth]

/-- Applied to an actual member of a join family, deficits sum to its excess. -/
theorem sum_join_deficit (S : Finset (Shape d h)) {r : Shape d h} (hr : r ∈ S) :
    ∑ k, (join S k - r.depth k) = excess S := by
  change ∑ k, deficit (join S) ⟨r, fun k => depth_le_join S hr k⟩ k = excess S
  exact sum_deficit (join S) ⟨r, fun k => depth_le_join S hr k⟩

/-- The coordinate deficits remain divisible by three. -/
theorem three_dvd_join_deficit (S : Finset (Shape d h)) (r : Shape d h)
    (k : Fin d) : 3 ∣ join S k - r.depth k :=
  Nat.dvd_sub (three_dvd_join S k) (r.three_dvd_depth k)

/-- Multi-indices of dyadic boxes with prescribed side depths. A coordinate
`i_k : Fin (2 ^ j k)` specifies the half-open side
`[i_k / 2^(j k), (i_k+1)/2^(j k))`. -/
abbrev CellIndices (j : Fin d → ℕ) := ∀ k : Fin d, Fin (2 ^ j k)

/-- Exact number of boxes of a prescribed depth vector. -/
theorem card_cellIndices (j : Fin d → ℕ) :
    Fintype.card (CellIndices j) = 2 ^ (∑ k, j k) := by
  simp only [CellIndices, Fintype.card_pi, Fintype.card_fin]
  exact Finset.prod_pow_eq_pow_sum Finset.univ j 2

/-- Exact number of boxes with a given shell shape. -/
theorem card_shellCells (r : Shape d h) :
    Fintype.card (CellIndices r.depth) = 2 ^ h := by
  rw [card_cellIndices, r.sum_depth]

/-- Product of the numbers of side intervals equals the number of join cells.
The bijection between these cells and admissible box families is separate. -/
theorem sideCounts_product (S : Finset (Shape d h)) (hS : S.Nonempty) :
    (∏ k, (2 : ℕ) ^ join S k) = 2 ^ (h + excess S) := by
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have hsum := excess_add_shell S hS
  unfold joinDepth at hsum
  omega

/-- The join cells have the `2^(h+e)` cardinality used in Lemma 4.2(a).
The correspondence with nonzero cell monomials remains a separate proof. -/
theorem card_joinCells (S : Finset (Shape d h)) (hS : S.Nonempty) :
    Fintype.card (CellIndices (join S)) = 2 ^ (h + excess S) := by
  rw [card_cellIndices]
  congr 1
  have hsum := excess_add_shell S hS
  unfold joinDepth at hsum
  omega

/-- Lower polynomial estimate used by the inverse Christoffel bound. -/
theorem christoffel_polynomial_lower (s : ℝ) :
    (1 : ℝ) / 7 ≤ 4 + 21 * s ^ 2 - 18 * s := by
  nlinarith [sq_nonneg (s - (3 : ℝ) / 7)]

/-- Upper polynomial estimate on a unit half-cell. -/
theorem christoffel_polynomial_upper (s : ℝ) (h0 : 0 ≤ s) (h1 : s ≤ 1) :
    4 + 21 * s ^ 2 - 18 * s ≤ 7 := by
  have hprod : 0 ≤ (1 - s) * (21 * s + 3) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

end Tusnady.Dyadic
