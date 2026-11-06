import Tusnady.Upper.LogComparison
import Tusnady.MainUnconditional
import Mathlib.Analysis.Asymptotics.Theta

/-!
# Formal consequences of the upper-bound target

These are proved implications. They do not assert that the upper-bound
premise has already been established. The actual lower bound is the existing,
unchanged unconditional theorem. No planar lower result is used.
-/
noncomputable section
open Filter
open scoped Topology
namespace Tusnady

/-- It suffices to prove the all-N goal for positive cardinalities. -/
theorem upperBound_of_positive_cardinality
    (h : ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 0 < N → worstDiscrepancy d N ≤ C * upperGrowth d N) :
    HigherDimensionalUpperBound := by
  intro d hd
  obtain ⟨C, hC, hbound⟩ := h d hd
  refine ⟨C, hC, fun N => ?_⟩
  by_cases hN : N = 0
  · subst N
    rw [worstDiscrepancy_zero (by omega)]
    exact mul_nonneg hC.le (upperGrowth_nonneg _ _)
  · exact hbound N (Nat.pos_of_ne_zero hN)

/-- The asymptotic form still supplies one coloring for all orthants. -/
theorem asymptoticUpperBound_real_colorings (h : AsymptoticUpperBound) :
    ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ P : Fin N → Point d, Function.Injective P →
        ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
          ∀ x : Point d, |realAnchoredCount P χ x| ≤ C * targetGrowth d N := by
  intro d hd
  obtain ⟨C, hC, N₀, hN₀, hbound⟩ := h d hd
  exact ⟨C, hC, N₀, hN₀, fun N hN =>
    (worstDiscrepancy_le_iff_real_colorings (by omega) N _).mp (hbound N hN)⟩

/-- The all-N upper statement also gives the usual Big-O statement. -/
theorem isBigO_of_upperBound (h : HigherDimensionalUpperBound) {d : ℕ} (hd : 2 ≤ d) :
    Asymptotics.IsBigO atTop (worstDiscrepancy d) (targetGrowth d) := by
  obtain ⟨C, _, N₀, hN₀, hbound⟩ := upperBound_implies_asymptotic h d hd
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hg : 0 ≤ targetGrowth d N := Real.rpow_nonneg
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg (worstDiscrepancy_nonneg (d := d) (by omega) N),
    abs_of_nonneg hg] using hbound N hN

/-- Generic combination of two-sided asymptotic bounds. -/
theorem lower_and_upper_imply_sharpOrder (hlower : HigherDimensionalLowerBound)
    (hupper : AsymptoticUpperBound) : SharpHigherDimensionalOrder := by
  intro d hd
  obtain ⟨c, hc, NL, _, hlower⟩ := hlower d hd
  obtain ⟨C, hC, NU, hNU, hupper⟩ := hupper d (by omega)
  refine ⟨c, C, hc, hC, max NL NU, hNU.trans (le_max_right _ _), fun N hN => ?_⟩
  exact ⟨hlower N ((le_max_left _ _).trans hN), hupper N ((le_max_right _ _).trans hN)⟩

/-- Once Nikolov's upper target is proved, the already proved lower bound
immediately yields the sharp order in every fixed d ≥ 3. -/
theorem sharpOrder_of_upperBound (hupper : HigherDimensionalUpperBound) :
    SharpHigherDimensionalOrder :=
  lower_and_upper_imply_sharpOrder main_lower_bound_unconditional
    (upperBound_implies_asymptotic hupper)

/-- Explicit positive two-sided constants give mathlib's actual Θ relation. -/
theorem isTheta_of_sharpOrder (h : SharpHigherDimensionalOrder) {d : ℕ} (hd : 3 ≤ d) :
    Asymptotics.IsTheta atTop (worstDiscrepancy d) (targetGrowth d) := by
  obtain ⟨c, C, hc, _, N₀, hN₀, hbound⟩ := h d hd
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hg : 0 ≤ targetGrowth d N := Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (worstDiscrepancy_nonneg (d := d) (by omega) N),
      abs_of_nonneg hg] using (hbound N hN).2
  · apply Asymptotics.IsBigO.of_bound (1/c)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hg : 0 ≤ targetGrowth d N := Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
    have hle : targetGrowth d N ≤ (1/c) * worstDiscrepancy d N := by
      have hraw := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using (hbound N hN).1)
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hraw
    simpa only [Real.norm_eq_abs, abs_of_nonneg (worstDiscrepancy_nonneg (d := d) (by omega) N),
      abs_of_nonneg hg] using hle

/-- The Θ conclusion remains explicitly dependent on the not-yet-closed
upper target until the actual upper proof is connected. -/
theorem isTheta_of_upperBound (hupper : HigherDimensionalUpperBound) {d : ℕ} (hd : 3 ≤ d) :
    Asymptotics.IsTheta atTop (worstDiscrepancy d) (targetGrowth d) :=
  isTheta_of_sharpOrder (sharpOrder_of_upperBound hupper) hd

end Tusnady
