import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# The dimension-dependent decay needed for error absorption

This is the scalar limit step in Main.pdf §7, not a proof of the analytic
remainder bound that produces its constant. Constants C and c are fixed
before h₀ and h are chosen. The exponent is d-2, so d≥3 is essential.
-/
namespace Tusnady

/-- All sufficiently large depths make the relative error at most c/2.
The order of quantifiers makes C and c independent of the shell depth. -/
theorem eventually_small_relative_error {d : ℕ} (hd : 3 ≤ d)
    {C c : ℝ} (hc : 0 < c) :
    ∃ h₀ : ℕ, ∀ h : ℕ, h₀ ≤ h →
      C / ((h : ℝ) + 1) ^ (d - 2) ≤ c / 2 := by
  obtain ⟨h₀, hh₀⟩ := exists_nat_gt (2 * C / c)
  refine ⟨h₀, ?_⟩
  intro h hh
  have hhh : (h₀ : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh
  have hx : 1 ≤ (h : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) h]
  have hpow : (h : ℝ) + 1 ≤ ((h : ℝ) + 1) ^ (d - 2) := by
    simpa using pow_le_pow_right₀ hx (show 1 ≤ d - 2 by omega)
  have hlarge : 2 * C / c < ((h : ℝ) + 1) ^ (d - 2) := by linarith
  have hmul : 2 * C < (((h : ℝ) + 1) ^ (d - 2)) * c :=
    (div_lt_iff₀ hc).1 hlarge
  have hp : 0 < ((h : ℝ) + 1) ^ (d - 2) := pow_pos (by positivity) _
  apply (div_le_iff₀ hp).2
  nlinarith

/-- The threshold can be chosen as a positive multiple of three. -/
theorem eventually_small_relative_error_on_shells {d : ℕ} (hd : 3 ≤ d)
    {C c : ℝ} (hc : 0 < c) :
    ∃ h₀ : ℕ, 0 < h₀ ∧ 3 ∣ h₀ ∧ ∀ h : ℕ, h₀ ≤ h →
      C / ((h : ℝ) + 1) ^ (d - 2) ≤ c / 2 := by
  obtain ⟨k, hk⟩ := eventually_small_relative_error hd hc
  refine ⟨3 * (k + 1), by omega, dvd_mul_right _ _, ?_⟩
  intro h hh
  exact hk h (by omega)

/-- Agreement of the natural-power and real negative-power formulas. -/
theorem relative_error_rpow_eq {d h : ℕ} (hd : 2 ≤ d) (C : ℝ) :
    C * Real.rpow ((h : ℝ) + 1) (-((d : ℝ) - 2)) =
      C / ((h : ℝ) + 1) ^ (d - 2) := by
  have he : (d : ℝ) - 2 = ((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hd]
    norm_num
  change C * (((h : ℝ) + 1) ^ (-((d : ℝ) - 2) : ℝ)) = _
  rw [he, Real.rpow_neg (show 0 ≤ (h : ℝ) + 1 by positivity),
    Real.rpow_natCast, div_eq_mul_inv]

end Tusnady
