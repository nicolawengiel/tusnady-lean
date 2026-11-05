import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # The actual small modulation parameter in Main.pdf (4.14)

The square-root formula is equivalent to the manuscript's real power.
The positive threshold is chosen explicitly before the depth `h`.
-/

noncomputable section
namespace Tusnady.RemainderParameters

def theta (d h : ℕ) (t : ℝ) : ℝ :=
  t / Real.sqrt (((h : ℝ) + 1) ^ (d - 2))

def lambda (d h : ℕ) (t : ℝ) : ℝ := (1 / 4 : ℝ) * theta d h t

theorem theta_eq_manuscript {d : ℕ} (hd : 2 ≤ d) (h : ℕ) (t : ℝ) :
    theta d h t = t * Real.rpow ((h : ℝ) + 1) (-((d : ℝ) - 2) / 2) := by
  unfold theta
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow,
    ← Real.rpow_natCast_mul (by positivity : 0 ≤ (h : ℝ) + 1),
    ← Real.rpow_neg (by positivity : 0 ≤ (h : ℝ) + 1)]
  congr 2
  rw [Nat.cast_sub hd]
  norm_num
  ring

theorem theta_sq (d h : ℕ) (t : ℝ) :
    theta d h t ^ 2 = t ^ 2 / ((h : ℝ) + 1) ^ (d - 2) := by
  unfold theta
  rw [div_pow, Real.sq_sqrt (by positivity)]

theorem theta_nonneg (d h : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ theta d h t := by
  exact div_nonneg ht (Real.sqrt_nonneg _)

theorem theta_pos (d h : ℕ) {t : ℝ} (ht : 0 < t) : 0 < theta d h t := by
  exact div_pos ht (Real.sqrt_pos.mpr (by positivity))

def threshold (d : ℕ) : ℝ :=
  min (1 / 2 : ℝ) (Real.sqrt (4 * Real.log 2 / (d : ℝ) ^ (d - 2)))

theorem threshold_pos {d : ℕ} (hd : 1 ≤ d) : 0 < threshold d := by
  unfold threshold
  apply lt_min (by norm_num)
  apply Real.sqrt_pos.mpr
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  exact div_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num))) (pow_pos hdpos _)

theorem threshold_le_half (d : ℕ) : threshold d ≤ 1 / 2 := min_le_left _ _

theorem threshold_budget {d : ℕ} (hd : 1 ≤ d) {t : ℝ}
    (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (1 / 4 : ℝ) ^ 2 * t ^ 2 * (d : ℝ) ^ (d - 2) ≤ Real.log 2 / 4 := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hp : 0 < (d : ℝ) ^ (d - 2) := pow_pos hdpos _
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htupper : t ≤ Real.sqrt (4 * Real.log 2 / (d : ℝ) ^ (d - 2)) :=
    htt.trans (min_le_right _ _)
  have hsquare : t ^ 2 ≤ 4 * Real.log 2 / (d : ℝ) ^ (d - 2) := by
    have hsq := sq_le_sq₀ ht (Real.sqrt_nonneg _) |>.mpr htupper
    rwa [Real.sq_sqrt (by positivity)] at hsq
  have hmul := (le_div_iff₀ hp).mp hsquare
  norm_num
  nlinarith

theorem excess_plus_one_le {d h e : ℕ} (hd : 1 ≤ d) (he : e ≤ (d - 1) * h) :
    (e : ℝ) + 1 ≤ (d : ℝ) * ((h : ℝ) + 1) := by
  have heN : e + 1 ≤ d * (h + 1) := by
    have hsplit : d = d - 1 + 1 := (Nat.sub_add_cancel hd).symm
    nlinarith
  exact_mod_cast heN

theorem activity_exponent_bound {d h e : ℕ} (hd : 2 ≤ d)
    (he : e ≤ (d - 1) * h) (t : ℝ) :
    lambda d h t ^ 2 * ((e : ℝ) + 1) ^ (d - 1) ≤
      ((1 / 4 : ℝ) ^ 2 * t ^ 2 * (d : ℝ) ^ (d - 2)) * ((e : ℝ) + 1) := by
  have hx : 0 < (h : ℝ) + 1 := by positivity
  have hE : 0 ≤ (e : ℝ) + 1 := by positivity
  have heq : d - 1 = (d - 2) + 1 := by omega
  have hp := pow_le_pow_left₀ hE (excess_plus_one_le (by omega) he) (d - 2)
  have hpow := mul_le_mul_of_nonneg_right hp hE
  rw [← pow_succ, ← heq, mul_pow] at hpow
  unfold lambda
  rw [mul_pow, theta_sq]
  have hden : 0 < ((h : ℝ) + 1) ^ (d - 2) := pow_pos hx _
  calc
    ((1 / 4 : ℝ) ^ 2 * (t ^ 2 / ((h : ℝ) + 1) ^ (d - 2))) *
        ((e : ℝ) + 1) ^ (d - 1) ≤
      ((1 / 4 : ℝ) ^ 2 * t ^ 2 *
        (((d : ℝ) ^ (d - 2) * ((h : ℝ) + 1) ^ (d - 2)) * ((e : ℝ) + 1))) /
          ((h : ℝ) + 1) ^ (d - 2) := by
      have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ (1 / 4 : ℝ) ^ 2 * t ^ 2 by positivity)
      have hdv := div_le_div_of_nonneg_right hm hden.le
      convert hdv using 1
      ring
    _ = _ := by field_simp [hden.ne']

theorem activity_exponent_small {d h e : ℕ} (hd : 2 ≤ d)
    (he : e ≤ (d - 1) * h) {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    lambda d h t ^ 2 * ((e : ℝ) + 1) ^ (d - 1) ≤
      (Real.log 2 / 4) * ((e : ℝ) + 1) :=
  (activity_exponent_bound hd he t).trans
    (mul_le_mul_of_nonneg_right (threshold_budget (by omega) ht htt) (by positivity))

end Tusnady.RemainderParameters
