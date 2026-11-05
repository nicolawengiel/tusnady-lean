import Tusnady.RemainderBlockActivity

/-! # The two activity bounds for the actual shape coefficients

These are the coefficients of the actual block-product test function.
The class-II coefficient bound and its activity sum are consequences of
the proved Walsh estimate and the proved finite block factorization.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
attribute [local instance] Classical.propDecidable
open Tusnady.RemainderActivity

def shapeSquareWeight (j : Fin d) (theta : ℝ) (a : BlockIndex h)
    (T : Finset (ShapesInBlock j a)) : ℝ :=
  (1 / 4 : ℝ) ^ 2 * Walsh.coefficient (Walsh.smoothedBlock theta) T ^ 2

theorem activeBlocks_eq_activity_active (j : Fin d) (S : Finset (BlockShape j h)) :
    activeBlocks j S = RemainderActivity.active S := rfl

theorem shapeCoefficient_sq_le_productWeight (j : Fin d) (theta : ℝ)
    (S : Finset (BlockShape j h)) :
    shapeCoefficient j theta S ^ 2 ≤ productWeight (shapeSquareWeight j theta) S := by
  rw [shapeCoefficient_formula]
  by_cases ho : Odd (activeBlocks j S).card
  · rw [if_pos ho, productWeight_eq_prod_active, ← activeBlocks_eq_activity_active]
    simp only [mul_pow, Finset.prod_pow, shapeSquareWeight, Finset.prod_mul_distrib,
      Finset.prod_const, ← pow_mul]
    rw [Nat.mul_comm (activeBlocks j S).card 2]
  · rw [if_neg ho, zero_pow (by norm_num)]
    apply Finset.prod_nonneg
    intro a _
    split_ifs
    · positivity
    · unfold shapeSquareWeight
      positivity

theorem shapeCoefficient_one_block (j : Fin d) (theta : ℝ)
    (S : Finset (BlockShape j h)) (a : BlockIndex h)
    (ha : activeBlocks j S = {a}) :
    shapeCoefficient j theta S = (1 / 4 : ℝ) *
      Walsh.coefficient (Walsh.smoothedBlock theta) (FiniteBlocks.fiber S a) := by
  rw [shapeCoefficient_formula, ha]
  norm_num

theorem restricted_shape_blockActivity_le (j : Fin d) {theta : ℝ} (htheta : 0 ≤ theta)
    (E : Finset (BlockShape j h)) (a : BlockIndex h) :
    blockActivity (restrictedWeight (shapeSquareWeight j theta) E) a ≤
      (1 / 4 : ℝ) ^ 2 * theta ^ 2 * (FiniteBlocks.fiber E a).card := by
  have heq : blockActivity (restrictedWeight (shapeSquareWeight j theta) E) a =
      (1 / 4 : ℝ) ^ 2 * ∑ T ∈ (Finset.univ : Finset (Finset (ShapesInBlock j a))).filter
        (fun T => T ⊆ FiniteBlocks.fiber E a ∧ T.Nonempty),
          Walsh.coefficient (Walsh.smoothedBlock theta) T ^ 2 := by
    unfold blockActivity
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    by_cases ht : T = ∅ <;> by_cases he : T ⊆ FiniteBlocks.fiber E a <;>
      simp [restrictedWeight, shapeSquareWeight, ht, he]
  rw [heq]
  have h := Walsh.smoothedBlock_first_activity htheta (FiniteBlocks.fiber E a)
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

theorem restricted_shape_activity_sum_le (j : Fin d) {theta : ℝ} (htheta : 0 ≤ theta)
    (E : Finset (BlockShape j h)) :
    (∑ a : BlockIndex h, blockActivity (restrictedWeight (shapeSquareWeight j theta) E) a) ≤
      (1 / 4 : ℝ) ^ 2 * theta ^ 2 * E.card := by
  calc
    _ ≤ ∑ a : BlockIndex h, (1 / 4 : ℝ) ^ 2 * theta ^ 2 * (FiniteBlocks.fiber E a).card :=
      Finset.sum_le_sum (fun a _ => restricted_shape_blockActivity_le j htheta E a)
    _ = _ := by rw [← Finset.mul_sum, ← Nat.cast_sum, sum_card_fiber]

/-- Main.pdf class I activity, for the actual smoothed-block Fourier
coefficients. The common coefficient is exactly `ε * coefficient` by
`shapeCoefficient_one_block`. -/
theorem one_block_third_activity (j : Fin d) {theta : ℝ} (htheta : 0 ≤ theta)
    (a : BlockIndex h) (E : Finset (ShapesInBlock j a)) :
    (∑ T ∈ (Finset.univ : Finset (Finset (ShapesInBlock j a))).filter
      (fun T => T ⊆ E ∧ 3 ≤ T.card),
        ((1 / 4 : ℝ) * Walsh.coefficient (Walsh.smoothedBlock theta) T) ^ 2) ≤
      (1 / 4 : ℝ) ^ 2 * theta ^ 6 * (E.card : ℝ) ^ 3 := by
  simp_rw [mul_pow]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left (Walsh.smoothedBlock_third_activity htheta E)
    (by positivity)).trans_eq (by ring)

/-- Actual class-II coefficient activity, with all allowed shape subsets
summed and with the join restriction expressed by the actual allowed set
`E`. The exponential has no depth-dependent hidden constant. -/
theorem shape_classII_activity_bound (j : Fin d) {theta : ℝ} (htheta : 0 ≤ theta)
    (E : Finset (BlockShape j h)) :
    (∑ S : Finset (BlockShape j h),
      if S ⊆ E ∧ 3 ≤ (activeBlocks j S).card then shapeCoefficient j theta S ^ 2 else 0) ≤
      (((1 / 4 : ℝ) ^ 2 * theta ^ 2 * E.card) ^ 3 / 6) *
        Real.exp ((1 / 4 : ℝ) ^ 2 * theta ^ 2 * E.card) := by
  let w := shapeSquareWeight (h := h) j theta
  let z := ∑ a : BlockIndex h, blockActivity (restrictedWeight w E) a
  have hz0 : 0 ≤ z := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro T _
    unfold restrictedWeight
    split_ifs
    · rfl
    · dsimp [w, shapeSquareWeight]
      positivity
    · rfl
  have hz : z ≤ (1 / 4 : ℝ) ^ 2 * theta ^ 2 * E.card :=
    restricted_shape_activity_sum_le j htheta E
  calc
    _ ≤ ∑ S : Finset (BlockShape j h),
        if S ⊆ E ∧ 3 ≤ (RemainderActivity.active S).card then productWeight w S else 0 := by
      apply Finset.sum_le_sum
      intro S _
      rw [activeBlocks_eq_activity_active]
      split_ifs
      · exact shapeCoefficient_sq_le_productWeight j theta S
      · rfl
    _ ≤ z ^ 3 / 6 * Real.exp z := restricted_active_tail_three_bound w (by
      intro a T
      dsimp [w, shapeSquareWeight]
      positivity) E
    _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right (pow_le_pow_left₀ hz0 hz 3) (by norm_num))
      (Real.exp_le_exp.mpr hz) (Real.exp_nonneg z) (by positivity)

end Tusnady.Witness
