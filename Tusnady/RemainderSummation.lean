import Tusnady.RemainderGrouping

/-! # Full actual shape-coefficient remainder summation

Both activity classes, actual joins, actual deficit counts, the fixed
modulation threshold, and the convergent excess majorant are combined.
There is no free coefficient/activity or remainder estimate hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
attribute [local instance] Classical.propDecidable
open Tusnady.RemainderParameters Tusnady.RemainderSeries Tusnady.RemainderCounting

theorem dyadicLength_eq_exp (e : ℕ) :
    DyadicFunctions.dyadicLength e = Real.exp (-Real.log 2 * e) := by
  unfold DyadicFunctions.dyadicLength
  have hexp : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  calc
    _ = (Real.exp (Real.log 2) ^ e)⁻¹ := by rw [hexp, one_div]
    _ = Real.exp (-((e : ℝ) * Real.log 2)) := by rw [← Real.exp_nat_mul, Real.exp_neg]
    _ = _ := by congr 1; ring

def joinWeight (d e : ℕ) : ℝ :=
  DyadicFunctions.dyadicLength e * ((e : ℝ) + 1) ^ (2 * (d - 1))

def groupedSeriesTerm (d h : ℕ) (t : ℝ) (e : ℕ) : ℝ :=
  (1 / 4 : ℝ) ^ 2 * theta d h t ^ 6 *
    (Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * d - 8)) +
  lambda d h t ^ 6 *
    (Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * (d - 1)) *
      Real.exp (lambda d h t ^ 2 * ((e : ℝ) + 1) ^ (d - 1)))

theorem groupedSeriesTerm_nonneg (d h : ℕ) (t : ℝ) (e : ℕ) :
    0 ≤ groupedSeriesTerm d h t e := by unfold groupedSeriesTerm; positivity

theorem join_weighted_activity_le (d h e : ℕ) (hd : 2 ≤ d) (p : Fin d)
    (j : Fin d → ℕ) (hj : ∑ i, j i = h + e) {t : ℝ} (ht : 0 ≤ t) :
    joinWeight d e * joinCoefficientActivity (h := h) p (theta d h t) j ≤
      groupedSeriesTerm d h t e := by
  have hw : 0 ≤ joinWeight d e := by
    unfold joinWeight
    exact mul_nonneg (DyadicFunctions.dyadicLength_pos _).le (by positivity)
  apply le_trans (mul_le_mul_of_nonneg_left
    (joinCoefficientActivity_bound d h e hd p j hj (theta_nonneg d h ht)) hw)
  rw [mul_add]
  unfold groupedSeriesTerm
  apply add_le_add
  · apply le_of_eq
    unfold joinWeight
    rw [dyadicLength_eq_exp,
      show 5 * d - 8 = 2 * (d - 1) + 3 * (d - 2) by omega, pow_add]
    ring
  · have hlambda : (1 / 4 : ℝ) ^ 2 * theta d h t ^ 2 = lambda d h t ^ 2 := by
      unfold lambda
      ring
    rw [hlambda, ← pow_mul, show 2 * 3 = 6 from rfl]
    unfold joinWeight
    rw [dyadicLength_eq_exp,
      show 5 * (d - 1) = 2 * (d - 1) + 3 * (d - 1) by omega, pow_add]
    have hnonneg : 0 ≤ lambda d h t ^ 6 * Real.exp (-Real.log 2 * e) *
        ((e : ℝ) + 1) ^ (2 * (d - 1)) * ((e : ℝ) + 1) ^ (3 * (d - 1)) *
          Real.exp (lambda d h t ^ 2 * ((e : ℝ) + 1) ^ (d - 1)) := by positivity
    nlinarith

theorem card_joins_excess_le_dim (d h e : ℕ) (hd : 1 ≤ d) (he : e ≤ (d - 1) * h) :
    Fintype.card (JoinVectors d (h + e)) ≤ d ^ (d - 1) * (h + 1) ^ (d - 1) := by
  cases d with
  | zero => omega
  | succ k => exact card_joins_excess_le k h e he

/-- The full finite coefficient sum after cell-location, in exactly the
scaling of Main.pdf Theorem 4.1. All joins and coefficients are actual. -/
theorem actual_shape_remainder_sum_bound (d h : ℕ) (hd : 2 ≤ d) (p : Fin d)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (∑ S : Finset (BlockShape p h), if 3 ≤ S.card then
      joinWeight d (shapeSetExcess p S) * shapeCoefficient p (theta d h t) S ^ 2 else 0) ≤
      ((d : ℝ) ^ (d - 1) * ((h : ℝ) + 1) ^ (d - 1)) *
        (sumBound d * lambda d h t ^ 2 * (theta d h t ^ 4 + lambda d h t ^ 4)) := by
  rw [shape_sum_group_by_join]
  have hper (e : Fin ((d - 1) * h + 1)) :
      (∑ j : JoinVectors d (h + e.val),
        joinWeight d e.val * joinCoefficientActivity (h := h) p (theta d h t)
          (fun i => (j.val i).val)) ≤
        ((d : ℝ) ^ (d - 1) * ((h : ℝ) + 1) ^ (d - 1)) * groupedSeriesTerm d h t e.val := by
    calc
      _ ≤ ∑ _j : JoinVectors d (h + e.val), groupedSeriesTerm d h t e.val := by
        apply Finset.sum_le_sum
        intro j _
        exact join_weighted_activity_le d h e.val hd p _ j.property.1 ht
      _ = (Fintype.card (JoinVectors d (h + e.val)) : ℝ) * groupedSeriesTerm d h t e.val := by simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (groupedSeriesTerm_nonneg d h t e.val)
        exact_mod_cast card_joins_excess_le_dim d h e.val (by omega)
          (by have := e.isLt; omega)
  rw [Fintype.sum_sigma]
  calc
    _ ≤ ∑ e : Fin ((d - 1) * h + 1),
        ((d : ℝ) ^ (d - 1) * ((h : ℝ) + 1) ^ (d - 1)) * groupedSeriesTerm d h t e.val :=
      Finset.sum_le_sum (fun e _ => hper e)
    _ = ((d : ℝ) ^ (d - 1) * ((h : ℝ) + 1) ^ (d - 1)) *
        (∑ e ∈ Finset.range ((d - 1) * h + 1), groupedSeriesTerm d h t e) := by
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold groupedSeriesTerm
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      exact numerical_remainder_sum_bound hd h ht htt

end Tusnady.Witness
