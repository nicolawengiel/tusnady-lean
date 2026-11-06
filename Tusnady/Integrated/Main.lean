import Tusnady.Integrated.Statements
import Tusnady.Integrated.Lower
import Tusnady.Boxes.Main

/-!
Combination of the three proved components: Wei in dimension two, the
preserved higher-dimensional lower bound, and Nikolov's upper bound.
No literature proposition occurs as a hypothesis of these theorems.
-/
noncomputable section
open Filter
namespace Tusnady.Integrated

theorem orthant_sharp_order : SharpOrder := by
  intro d hd
  obtain ⟨c, hc, NL, _, hL⟩ := lower_bound d hd
  obtain ⟨C, hC, NU, hNU, hU⟩ := Tusnady.main_upper_bound_asymptotic d hd
  exact ⟨c, C, hc, hC, max NL NU, hNU.trans (le_max_right _ _),
    fun N hN => ⟨hL N ((le_max_left _ _).trans hN),
      hU N ((le_max_right _ _).trans hN)⟩⟩

theorem main_sharp_order : CombinedSharpOrder := by
  intro d hd
  obtain ⟨c, C, hc, hC, N₀, hN₀, hbound⟩ := orthant_sharp_order d hd
  refine ⟨c, (2 : ℝ)^d * C, hc, mul_pos (by positivity) hC, N₀, hN₀, ?_⟩
  intro N hN
  refine ⟨(hbound N hN).1, Boxes.orthant_worstDiscrepancy_le (by omega) N, ?_⟩
  calc
    Boxes.worstDiscrepancy d N ≤ (2 : ℝ)^d * Tusnady.worstDiscrepancy d N :=
      Boxes.worstDiscrepancy_le_orthant (by omega) N
    _ ≤ (2 : ℝ)^d * (C * targetGrowth d N) :=
      mul_le_mul_of_nonneg_left (hbound N hN).2 (by positivity)
    _ = _ := by ring

theorem boxes_sharp_order : BoxSharpOrder := by
  intro d hd
  obtain ⟨c, C, hc, hC, N₀, hN₀, h⟩ := main_sharp_order d hd
  exact ⟨c, C, hc, hC, N₀, hN₀, fun N hN =>
    ⟨(h N hN).1.trans (h N hN).2.1, (h N hN).2.2⟩⟩

theorem boxes_upper_bound_real_colorings : BoxColoringUpperBound := by
  intro d hd
  obtain ⟨C, hC, hbound⟩ := Boxes.main_upper_bound_real_colorings d hd
  refine ⟨C, hC, fun N P hP => ?_⟩
  obtain ⟨χ, hχ, h⟩ := hbound N P hP
  exact ⟨χ, hχ, Boxes.abs_realCountCorners_le_of_queries P χ _ h⟩

theorem boxes_lower_bound_real_colorings : BoxWitnessLowerBound := by
  intro d hd
  obtain ⟨c, hc, N₀, hN₀, hbound⟩ := lower_bound_real_colorings d hd
  refine ⟨c, hc, N₀, hN₀, fun N hN => ?_⟩
  obtain ⟨P, hP, h⟩ := hbound N hN
  refine ⟨P, hP, fun χ hχ => ?_⟩
  obtain ⟨x, hx⟩ := h χ hχ
  let q := Boxes.orthantQuery P x
  have heq : Boxes.realCountCorners P χ q.lower q.upper = realAnchoredCount P χ x := by
    change Boxes.realCount P χ (Boxes.orthantQuery P x) = _
    unfold Boxes.realCount realAnchoredCount
    rw [Boxes.trace_orthantQuery]
  exact ⟨q.lower, q.upper, q.valid, by simpa only [heq] using hx⟩

theorem orthant_isTheta {d : ℕ} (hd : 2 ≤ d) :
    Asymptotics.IsTheta atTop (Tusnady.worstDiscrepancy d) (targetGrowth d) := by
  obtain ⟨c, C, hc, _, N₀, hN₀, hbound⟩ := orthant_sharp_order d hd
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hg : 0 ≤ targetGrowth d N := Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (Tusnady.worstDiscrepancy_nonneg (d := d) (by omega) N), abs_of_nonneg hg]
      using (hbound N hN).2
  · apply Asymptotics.IsBigO.of_bound (1/c)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hg : 0 ≤ targetGrowth d N := Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
    have hle : targetGrowth d N ≤ (1/c) * Tusnady.worstDiscrepancy d N := by
      have hraw := (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using (hbound N hN).1)
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hraw
    simpa only [Real.norm_eq_abs, abs_of_nonneg
      (Tusnady.worstDiscrepancy_nonneg (d := d) (by omega) N), abs_of_nonneg hg] using hle

theorem boxes_isTheta {d : ℕ} (hd : 2 ≤ d) :
    Asymptotics.IsTheta atTop (Boxes.worstDiscrepancy d) (targetGrowth d) :=
  (Boxes.worstDiscrepancy_isTheta_orthant (by omega)).trans (orthant_isTheta hd)

end Tusnady.Integrated
