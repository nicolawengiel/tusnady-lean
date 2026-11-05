import Tusnady.RemainderParameters

/-! # Convergent excess majorants for the actual modulation parameter

The infinite bound depends only on dimension. Every finite excess sum is
bounded uniformly in the depth and in `0≤t≤threshold d`.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.RemainderSeries
open Tusnady.RemainderParameters

theorem summable_shifted_pow_exp (k : ℕ) {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * Real.exp (-r * n)) := by
  have h := (Real.summable_pow_mul_exp_neg_nat_mul k hr).comp_injective
    (i := fun n : ℕ => n + 1) (fun a b h => by dsimp only at h; omega)
  have hm := h.mul_left (Real.exp r)
  convert hm using 1
  funext n
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have heq : Real.exp r * Real.exp (-r * ((n : ℝ) + 1)) = Real.exp (-r * n) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((n : ℝ) + 1) ^ k * (Real.exp r * Real.exp (-r * ((n : ℝ) + 1))) := by rw [heq]
    _ = _ := by ring

def majorant (d e : ℕ) : ℝ :=
  Real.exp (Real.log 2 / 4) * (((e : ℝ) + 1) ^ (5 * (d - 1)) *
    Real.exp (-(3 * Real.log 2 / 4) * e))

theorem majorant_nonneg (d e : ℕ) : 0 ≤ majorant d e := by unfold majorant; positivity

theorem majorant_summable (d : ℕ) : Summable (majorant d) := by
  apply (summable_shifted_pow_exp (5 * (d - 1))
    (show 0 < 3 * Real.log 2 / 4 by positivity)).mul_left

def sumBound (d : ℕ) : ℝ := ∑' e : ℕ, majorant d e

theorem sumBound_nonneg (d : ℕ) : 0 ≤ sumBound d := tsum_nonneg (majorant_nonneg d)

theorem sumBound_pos (d : ℕ) : 0 < sumBound d := by
  have h := (majorant_summable d).sum_le_tsum {0} (fun e _ => majorant_nonneg d e)
  have h0 : 0 < majorant d 0 := by unfold majorant; positivity
  have hs : majorant d 0 ≤ sumBound d := by simpa only [Finset.sum_singleton, sumBound] using h
  exact h0.trans_le hs

theorem finite_majorant_sum_le (d H : ℕ) :
    (∑ e ∈ Finset.range (H + 1), majorant d e) ≤ sumBound d :=
  (majorant_summable d).sum_le_tsum _ (fun e _ => majorant_nonneg d e)

theorem majorant_eq (d e : ℕ) :
    majorant d e = Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * (d - 1)) *
      Real.exp ((Real.log 2 / 4) * ((e : ℝ) + 1)) := by
  unfold majorant
  have heq : Real.exp (Real.log 2 / 4) * Real.exp (-(3 * Real.log 2 / 4) * e) =
      Real.exp (-Real.log 2 * e) * Real.exp ((Real.log 2 / 4) * ((e : ℝ) + 1)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((e : ℝ) + 1) ^ (5 * (d - 1)) *
        (Real.exp (Real.log 2 / 4) * Real.exp (-(3 * Real.log 2 / 4) * e)) := by ring
    _ = _ := by rw [heq]; ring

theorem classI_term_le {d : ℕ} (hd : 2 ≤ d) (e : ℕ) :
    Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * d - 8) ≤ majorant d e := by
  rw [majorant_eq]
  have hp : ((e : ℝ) + 1) ^ (5 * d - 8) ≤ ((e : ℝ) + 1) ^ (5 * (d - 1)) :=
    pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) e]) (by omega)
  have he : 1 ≤ Real.exp ((Real.log 2 / 4) * ((e : ℝ) + 1)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  exact (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)).trans
    (le_mul_of_one_le_right (by positivity) he)

theorem classI_sum_le {d : ℕ} (hd : 2 ≤ d) (H : ℕ) :
    (∑ e ∈ Finset.range (H + 1),
      Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * d - 8)) ≤ sumBound d :=
  (Finset.sum_le_sum (fun e _ => classI_term_le hd e)).trans (finite_majorant_sum_le d H)

theorem classII_term_le {d h e : ℕ} (hd : 2 ≤ d) (he : e ≤ (d - 1) * h)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * (d - 1)) *
      Real.exp (lambda d h t ^ 2 * ((e : ℝ) + 1) ^ (d - 1)) ≤ majorant d e := by
  rw [majorant_eq]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (activity_exponent_small hd he ht htt))
    (by positivity)

theorem classII_sum_le {d : ℕ} (hd : 2 ≤ d) (h : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (∑ e ∈ Finset.range ((d - 1) * h + 1),
      Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * (d - 1)) *
        Real.exp (lambda d h t ^ 2 * ((e : ℝ) + 1) ^ (d - 1))) ≤ sumBound d := by
  apply le_trans _ (finite_majorant_sum_le d ((d - 1) * h))
  apply Finset.sum_le_sum
  intro e he
  exact classII_term_le hd (by have := Finset.mem_range.mp he; omega) ht htt

/-- Final scalar combination of both class sums. There is no analytic
remainder hypothesis here: the actual displayed finite numerical sum is
bounded in the form required by Theorem 4.1. -/
theorem numerical_remainder_sum_bound {d : ℕ} (hd : 2 ≤ d) (h : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (1 / 4 : ℝ) ^ 2 * theta d h t ^ 6 *
      (∑ e ∈ Finset.range ((d - 1) * h + 1),
        Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * d - 8)) +
      lambda d h t ^ 6 *
        (∑ e ∈ Finset.range ((d - 1) * h + 1),
          Real.exp (-Real.log 2 * e) * ((e : ℝ) + 1) ^ (5 * (d - 1)) *
            Real.exp (lambda d h t ^ 2 * ((e : ℝ) + 1) ^ (d - 1))) ≤
      sumBound d * lambda d h t ^ 2 * (theta d h t ^ 4 + lambda d h t ^ 4) := by
  calc
    _ ≤ (1 / 4 : ℝ) ^ 2 * theta d h t ^ 6 * sumBound d + lambda d h t ^ 6 * sumBound d :=
      add_le_add (mul_le_mul_of_nonneg_left (classI_sum_le hd _) (by positivity))
        (mul_le_mul_of_nonneg_left (classII_sum_le hd h ht htt) (by positivity))
    _ = _ := by unfold lambda; ring

end Tusnady.RemainderSeries
