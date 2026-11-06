import Tusnady.Upper.Statements

/-!
# Regularized and asymptotic logarithmic growth

All statements here are elementary consequences of the exact target
propositions. No geometric or vector-balancing theorem is assumed or proved
by defining those propositions.
-/
noncomputable section
namespace Tusnady

lemma dimension_exponent_nonneg {d : ℕ} (hd : 1 ≤ d) :
    0 ≤ (d : ℝ) - (1 / 2 : ℝ) := by
  have hd' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  linarith

lemma log_two_add_nat_le_two_log {N : ℕ} (hN : 2 ≤ N) :
    Real.log (2 + (N : ℝ)) ≤ 2 * Real.log (N : ℝ) := by
  have hN' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : 2 + (N : ℝ) ≤ (N : ℝ)^2 := by nlinarith
  calc
    Real.log (2 + (N : ℝ)) ≤ Real.log ((N : ℝ)^2) :=
      Real.log_le_log (by positivity) hsq
    _ = 2 * Real.log (N : ℝ) := by rw [Real.log_pow]; norm_num

lemma targetGrowth_le_upperGrowth {d N : ℕ} (hd : 1 ≤ d) (hN : 1 ≤ N) :
    targetGrowth d N ≤ upperGrowth d N := by
  have hN' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  exact Real.rpow_le_rpow (Real.log_nonneg hN')
    (Real.log_le_log (by positivity) (by linarith)) (dimension_exponent_nonneg hd)

lemma upperGrowth_le_two_rpow_mul_targetGrowth {d N : ℕ}
    (hd : 1 ≤ d) (hN : 2 ≤ N) :
    upperGrowth d N ≤ Real.rpow 2 ((d : ℝ) - (1 / 2 : ℝ)) * targetGrowth d N := by
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  calc
    upperGrowth d N ≤ Real.rpow (2 * Real.log (N : ℝ)) ((d : ℝ) - (1/2:ℝ)) :=
      Real.rpow_le_rpow (Real.log_nonneg (by
        have hn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith))
        (log_two_add_nat_le_two_log hN) (dimension_exponent_nonneg hd)
    _ = _ := Real.mul_rpow (by norm_num) hlog

lemma upperGrowth_mono_nat {d M N : ℕ} (hd : 1 ≤ d) (hMN : M ≤ N) :
    upperGrowth d M ≤ upperGrowth d N := by
  have hMN' : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
  exact Real.rpow_le_rpow (Real.log_nonneg (by
    have hm : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith))
    (Real.log_le_log (by positivity) (by linarith)) (dimension_exponent_nonneg hd)

/-- An all-N bound immediately gives the usual log N asymptotic bound. -/
theorem upperBound_implies_asymptotic (h : HigherDimensionalUpperBound) :
    AsymptoticUpperBound := by
  intro d hd
  obtain ⟨C, hC, hbound⟩ := h d hd
  refine ⟨C * Real.rpow 2 ((d : ℝ) - (1/2:ℝ)),
    mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), 2, le_rfl, ?_⟩
  intro N hN
  calc
    worstDiscrepancy d N ≤ C * upperGrowth d N := hbound N
    _ ≤ C * (Real.rpow 2 ((d : ℝ) - (1/2:ℝ)) * targetGrowth d N) :=
      mul_le_mul_of_nonneg_left (upperGrowth_le_two_rpow_mul_targetGrowth (by omega) hN) hC.le
    _ = _ := by ring

/-- Conversely an asymptotic bound can absorb finitely many small N into a
new dimension-dependent constant. In particular zero points cause no exception. -/
theorem asymptotic_implies_upperBound (h : AsymptoticUpperBound) :
    HigherDimensionalUpperBound := by
  intro d hd
  obtain ⟨C, hC, N₀, hN₀, hbound⟩ := h d hd
  let C' := max C ((N₀ : ℝ) / upperGrowth d 0)
  have hCC' : C ≤ C' := le_max_left _ _
  have hC' : 0 < C' := hC.trans_le hCC'
  refine ⟨C', hC', fun N => ?_⟩
  by_cases hN : N₀ ≤ N
  · calc
      worstDiscrepancy d N ≤ C * targetGrowth d N := hbound N hN
      _ ≤ C * upperGrowth d N := mul_le_mul_of_nonneg_left
        (targetGrowth_le_upperGrowth (by omega) (by omega)) hC.le
      _ ≤ C' * upperGrowth d N := mul_le_mul_of_nonneg_right hCC' (upperGrowth_nonneg _ _)
  · have hNN₀ : (N : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast (Nat.le_of_lt (lt_of_not_ge hN))
    have hconst : (N₀ : ℝ) ≤ C' * upperGrowth d 0 := by
      exact (div_le_iff₀ (upperGrowth_pos d 0)).mp (le_max_right _ _)
    calc
      worstDiscrepancy d N ≤ (N : ℝ) := worstDiscrepancy_le_card (by omega) N
      _ ≤ (N₀ : ℝ) := hNN₀
      _ ≤ C' * upperGrowth d 0 := hconst
      _ ≤ C' * upperGrowth d N := mul_le_mul_of_nonneg_left
        (upperGrowth_mono_nat (by omega) (Nat.zero_le N)) hC'.le

theorem upper_iff_asymptoticUpperBound :
    HigherDimensionalUpperBound ↔ AsymptoticUpperBound :=
  ⟨upperBound_implies_asymptotic, asymptotic_implies_upperBound⟩

end Tusnady
