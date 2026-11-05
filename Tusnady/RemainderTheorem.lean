import Tusnady.CellReindex
import Tusnady.RemainderSummation

/-! # The actual higher-dimensional cubic remainder estimate

Actual product-uniform Parseval, the actual bounded primitive-high map,
actual cell-location, both activity classes and all excess sums are
combined. No additional analytic or coefficient hypothesis is used.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Tusnady.Witness
attribute [local instance] Classical.propDecidable
open Tusnady.RemainderParameters Tusnady.RemainderSeries

def remainderConstant (d : ℕ) : ℝ :=
  Cell.cellLocationConstant d * (d : ℝ) ^ (d - 1) * sumBound d

theorem remainderConstant_pos {d : ℕ} (hd : 1 ≤ d) : 0 < remainderConstant d := by
  unfold remainderConstant
  exact mul_pos (mul_pos (Cell.cellLocationConstant_pos d)
    (pow_pos (by exact_mod_cast (show 0 < d by omega)) _)) (sumBound_pos d)

theorem fixed_shape_cubic_energy_le (d h : ℕ) (hd : 0 < d) (theta : ℝ)
    (S : Finset (BlockShape (⟨0,hd⟩ : Fin d) h)) :
    (∑ c : CellChoice S, cubicCoefficient ⟨0,hd⟩ theta ⟨S,c⟩ ^ 2 *
      (1 / 3 : ℝ) ^ (variableSet ⟨S,c⟩).card *
      ‖Haar.primitiveHighCLM d (h+3*d) h (cellL2Vector ⟨S,c⟩)‖ ^ 2) ≤
      (Cell.cellLocationConstant d * DyadicFunctions.dyadicLength h ^ 2) *
        (if 3 ≤ S.card then joinWeight d (shapeSetExcess ⟨0,hd⟩ S) *
          shapeCoefficient ⟨0,hd⟩ theta S ^ 2 else 0) := by
  by_cases h3 : 3 ≤ S.card
  · simp only [cubicCoefficient, if_pos h3]
    by_cases hc : shapeCoefficient ⟨0,hd⟩ theta S = 0
    · simp [hc]
    have henergy := cell_sum_energy_bound_dim d hd theta S hc
    calc
      _ ≤ ∑ c : CellChoice S, shapeCoefficient ⟨0,hd⟩ theta S ^ 2 *
          ‖Haar.primitiveHighCLM d (h+3*d) h (cellL2Vector ⟨S,c⟩)‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro c _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_of_le_one_right (sq_nonneg _)
          (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num))
      _ = shapeCoefficient ⟨0,hd⟩ theta S ^ 2 *
          (∑ c : CellChoice S, ‖Haar.primitiveHighCLM d (h+3*d) h
            (cellL2Vector ⟨S,c⟩)‖ ^ 2) := (Finset.mul_sum _ _ _).symm
      _ ≤ shapeCoefficient ⟨0,hd⟩ theta S ^ 2 *
          (Cell.cellLocationConstant d * DyadicFunctions.dyadicLength h ^ 2 *
            DyadicFunctions.dyadicLength (shapeSetExcess ⟨0,hd⟩ S) *
              ((shapeSetExcess ⟨0,hd⟩ S : ℝ) + 1) ^ (2 * (d - 1))) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simpa only [physicalShapes, shapeSetExcess, Nat.cast_add, Nat.cast_one] using henergy
      _ = _ := by unfold joinWeight; ring
  · simp [cubicCoefficient, h3]

/-- Main.pdf Theorem 4.1 for the actual L² class of `W-Wlin` after the
actual high projection and primitive. All constants depend only on `d`;
the entire interval `0≤t≤threshold d` is covered. -/
theorem expected_actual_cubic_remainder_sq (d h : ℕ) (hd : 2 ≤ d)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (∫ u, ‖Haar.primitiveHighCLM d (h+3*d) h
      (cubicTestL2 (⟨0,by omega⟩ : Fin d) (theta d h t) u)‖ ^ 2
        ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      remainderConstant d * lambda d h t ^ 2 * ((h : ℝ) + 1) ^ (d - 1) *
        DyadicFunctions.dyadicLength h ^ 2 * (theta d h t ^ 4 + lambda d h t ^ 4) := by
  rw [expected_cubic_operator_sq, Fintype.sum_sigma]
  have hconst : 0 ≤ Cell.cellLocationConstant d * DyadicFunctions.dyadicLength h ^ 2 :=
    mul_nonneg (Cell.cellLocationConstant_pos d).le (sq_nonneg _)
  calc
    _ ≤ ∑ S : Finset (BlockShape (⟨0,by omega⟩ : Fin d) h),
        (Cell.cellLocationConstant d * DyadicFunctions.dyadicLength h ^ 2) *
          (if 3 ≤ S.card then joinWeight d (shapeSetExcess ⟨0,by omega⟩ S) *
            shapeCoefficient ⟨0,by omega⟩ (theta d h t) S ^ 2 else 0) :=
      Finset.sum_le_sum (fun S _ => fixed_shape_cubic_energy_le d h (by omega) (theta d h t) S)
    _ = (Cell.cellLocationConstant d * DyadicFunctions.dyadicLength h ^ 2) *
        (∑ S : Finset (BlockShape (⟨0,by omega⟩ : Fin d) h),
          if 3 ≤ S.card then joinWeight d (shapeSetExcess ⟨0,by omega⟩ S) *
            shapeCoefficient ⟨0,by omega⟩ (theta d h t) S ^ 2 else 0) := by rw [Finset.mul_sum]
    _ ≤ (Cell.cellLocationConstant d * DyadicFunctions.dyadicLength h ^ 2) *
        (((d : ℝ) ^ (d - 1) * ((h : ℝ) + 1) ^ (d - 1)) *
          (sumBound d * lambda d h t ^ 2 * (theta d h t ^ 4 + lambda d h t ^ 4))) :=
      mul_le_mul_of_nonneg_left (actual_shape_remainder_sum_bound d h hd ⟨0,by omega⟩ ht htt) hconst
    _ = _ := by unfold remainderConstant; ring

end Tusnady.Witness
