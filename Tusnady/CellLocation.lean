import Tusnady.CellMassBounds

/-!
# The actual analytic cell-location estimate

This is Manuscript Lemma 4.3 for the concrete mixed cell functions after
identifying the shell-box families with their cells. All analytic components,
retention, primitive integrals, and retained counts are proved here. The
separate shell-family-to-cell factorization is handled by CellGeometry.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.DyadicFunctions Tusnady.Haar
open scoped BigOperators

/-- Explicit constant depending only on dimension. -/
def cellLocationConstant (d : ℕ) : ℝ :=
  (((2*d+1:ℕ):ℝ)^(2*(d-1)))*(2:ℝ)^(2*d)

lemma cellLocationConstant_pos (d : ℕ) : 0 < cellLocationConstant d := by
  unfold cellLocationConstant
  positivity

/-- Actual primitive norm of one cell, before summing over all cell positions. -/
theorem single_cell_location {n H : ℕ} (h e : ℕ) (j : Fin (n+1) → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin (n+1) → Bool)
    (hjoin : ∑ k, j k = h+e) (hm0 : m 0 = true) :
    (∫ p, Tusnady.boxPrimitive (highProjection (n+1) H h (cellL2 j hj I m)) p^2 ∂cubeMeasure (n+1)) ≤
      cellLocationConstant (n+1)*dyadicLength h^3*dyadicLength e^2*((e+1:ℕ):ℝ)^(2*n) := by
  let B : ℝ := (2:ℝ)^(2*(n+1))*dyadicLength h^3*dyadicLength e^2
  have hB : 0 ≤ B := by
    dsimp [B]
    have hh := dyadicLength_pos h
    have he := dyadicLength_pos e
    positivity
  have hcNat := retained_card_le_polynomial h e j hj I m hjoin hm0
  have hc : ((retainedComponents h j hj I m).card:ℝ) ≤
      (((2*(n+1)+1:ℕ):ℝ)^n)*(((e+1:ℕ):ℝ)^n) := by exact_mod_cast hcNat
  calc
    _ ≤ ((retainedComponents h j hj I m).card:ℝ)^2*B :=
      integral_high_cell_le_card_sq h j hj I m B
        (fun b hb => retained_componentMass_le h e j hj I m hjoin b hb)
    _ ≤ ((((2*(n+1)+1:ℕ):ℝ)^n)*(((e+1:ℕ):ℝ)^n))^2*B := by
      apply mul_le_mul_of_nonneg_right _ hB
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
    _ = _ := by
      dsimp [B]
      unfold cellLocationConstant
      simp only [Nat.add_sub_cancel_right]
      rw [show 2*n = n*2 by omega]
      simp only [pow_mul]
      ring

lemma volume_rescale (h e : ℕ) :
    (2:ℝ)^(h+e)*dyadicLength h^3*dyadicLength e^2 = dyadicLength h^2*dyadicLength e := by
  rw [pow_add]
  calc
    _ = dyadicLength h^2*dyadicLength e*
        (dyadicLength h*(2:ℝ)^h)*(dyadicLength e*(2:ℝ)^e) := by ring
    _ = _ := by rw [dyadicLength_mul_pow, dyadicLength_mul_pow]; ring

/-- The full analytic cell-location estimate, with a constant independent
of h, e, join depths, cell locations, and the modulation pattern. -/
theorem cell_location_succ {n H : ℕ} (h e : ℕ) (j : Fin (n+1) → ℕ)
    (hj : ∀ k, j k+2 < H) (m : Fin (n+1) → Bool)
    (hjoin : ∑ k, j k = h+e) (hm0 : m 0 = true) :
    (∑ I : Tusnady.Dyadic.CellIndices j,
      ∫ p, Tusnady.boxPrimitive (highProjection (n+1) H h (cellL2 j hj I m)) p^2 ∂cubeMeasure (n+1)) ≤
      cellLocationConstant (n+1)*dyadicLength h^2*dyadicLength e*((e+1:ℕ):ℝ)^(2*n) := by
  calc
    _ ≤ ∑ _I : Tusnady.Dyadic.CellIndices j,
        cellLocationConstant (n+1)*dyadicLength h^3*dyadicLength e^2*((e+1:ℕ):ℝ)^(2*n) := by
      apply Finset.sum_le_sum
      intro I _
      exact single_cell_location h e j hj I m hjoin hm0
    _ = (Fintype.card (Tusnady.Dyadic.CellIndices j):ℝ)*
        (cellLocationConstant (n+1)*dyadicLength h^3*dyadicLength e^2*((e+1:ℕ):ℝ)^(2*n)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (2:ℝ)^(h+e)*
        (cellLocationConstant (n+1)*dyadicLength h^3*dyadicLength e^2*((e+1:ℕ):ℝ)^(2*n)) := by
      rw [Tusnady.Dyadic.card_cellIndices, hjoin]
      push_cast
      rfl
    _ = _ := by
      calc
        _ = cellLocationConstant (n+1)*
            ((2:ℝ)^(h+e)*dyadicLength h^3*dyadicLength e^2)*((e+1:ℕ):ℝ)^(2*n) := by ring
        _ = _ := by rw [volume_rescale]; ring

/-- Dimension-d formulation. For v=2^(-h), this is exactly
C_d v² 2^(-e)(e+1)^(2(d-1)), the target in Manuscript Lemma 4.3. -/
theorem cell_location (d H h e : ℕ) (hd : 0 < d) (j : Fin d → ℕ)
    (hj : ∀ k, j k+2 < H) (m : Fin d → Bool)
    (hjoin : ∑ k, j k = h+e) (hm0 : m ⟨0,hd⟩ = true) :
    (∑ I : Tusnady.Dyadic.CellIndices j,
      ∫ p, Tusnady.boxPrimitive (highProjection d H h (cellL2 j hj I m)) p^2 ∂cubeMeasure d) ≤
      cellLocationConstant d*dyadicLength h^2*dyadicLength e*((e+1:ℕ):ℝ)^(2*(d-1)) := by
  cases d with
  | zero => omega
  | succ n =>
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right] using
      cell_location_succ h e j hj m hjoin hm0

end Tusnady.Cell
