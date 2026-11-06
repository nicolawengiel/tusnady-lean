import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! An explicit logarithmic bound for the binary-tree factorization depth. -/
noncomputable section
namespace Tusnady.Upper.DyadicFactorization

def depth (N : ℕ) : ℕ := Nat.log 2 (N+1)+1

def factorConstant (s : ℕ) : ℝ := (3 / Real.log 2)^s

lemma factorConstant_pos (s : ℕ) : 0 < factorConstant s := by
  apply pow_pos
  exact div_pos (by norm_num) (Real.log_pos (by norm_num))

lemma depth_large (N : ℕ) : N < 2^(depth N) := by
  exact lt_trans (Nat.lt_succ_self N) (Nat.lt_pow_succ_log_self (by norm_num) (N+1))

lemma depth_log_bound (N : ℕ) :
    ((depth N+1 : ℕ) : ℝ) ≤ (3 / Real.log 2) * Real.log (N+2) := by
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : (2:ℝ)^(Nat.log 2 (N+1)) ≤ (N+1 : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.succ_ne_zero N)
  have hlog : (Nat.log 2 (N+1):ℝ) * Real.log 2 ≤ Real.log (N+1) := by
    simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpow
  have hm : Real.log (N+1) ≤ Real.log (N+2) := Real.log_le_log (by positivity) (by linarith)
  have htwo : Real.log 2 ≤ Real.log (N+2) := Real.log_le_log (by norm_num) (by have hn := Nat.cast_nonneg (α := ℝ) N; linarith)
  have hmul : ((depth N+1 : ℕ) : ℝ) * Real.log 2 ≤ 3 * Real.log (N+2) := by
    dsimp [depth]
    push_cast
    nlinarith
  calc
    ((depth N+1 : ℕ) : ℝ) ≤ (3 * Real.log (N+2)) / Real.log 2 := (le_div_iff₀ hp).mpr hmul
    _ = _ := by ring

lemma depth_pow_log_bound (s N : ℕ) :
    ((depth N+1 : ℕ) : ℝ)^s ≤ factorConstant s * (Real.log (N+2))^s := by
  calc
    _ ≤ ((3 / Real.log 2) * Real.log (N+2))^s :=
      pow_le_pow_left₀ (by positivity) (depth_log_bound N) s
    _ = _ := by rw [mul_pow]; rfl

end Tusnady.Upper.DyadicFactorization
