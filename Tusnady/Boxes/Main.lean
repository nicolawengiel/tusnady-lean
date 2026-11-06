import Tusnady.Boxes.OrthantComparison
import Tusnady.Upper.Main

/-!
# Consequences for all closed bounded boxes

The existing orthant theorem is transferred with the fixed dimensional factor
`2^d`. No discrepancy definition of the original development is changed.
This file does not use or assert a planar lower-bound result.
-/
noncomputable section
namespace Tusnady.Boxes

def UpperBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, worstDiscrepancy d N ≤ C * upperGrowth d N

def ColoringUpperBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∀ P : Fin N → Point d, Function.Injective P →
      ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
        ∀ q : Query d, |realCount P χ q| ≤ C * upperGrowth d N

def AsymptoticUpperBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → worstDiscrepancy d N ≤ C * targetGrowth d N

def SharpOrder : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * targetGrowth d N ≤ worstDiscrepancy d N ∧
        worstDiscrepancy d N ≤ C * targetGrowth d N

theorem main_upper_bound : UpperBound := by
  intro d hd
  obtain ⟨C, hC, hbound⟩ := Tusnady.main_upper_bound d hd
  refine ⟨(2 : ℝ)^d * C, mul_pos (by positivity) hC, fun N => ?_⟩
  calc
    worstDiscrepancy d N ≤ (2 : ℝ)^d * Tusnady.worstDiscrepancy d N :=
      worstDiscrepancy_le_orthant (by omega) N
    _ ≤ (2 : ℝ)^d * (C * upperGrowth d N) :=
      mul_le_mul_of_nonneg_left (hbound N) (by positivity)
    _ = _ := by ring

/-- A single coloring works for every valid pair of finite real corners,
including degenerate boxes and every N, including zero. -/
theorem main_upper_bound_real_colorings : ColoringUpperBound := by
  intro d hd
  obtain ⟨C, hC, hbound⟩ := Tusnady.main_upper_bound_real_colorings d hd
  refine ⟨(2 : ℝ)^d * C, mul_pos (by positivity) hC, ?_⟩
  intro N P hP
  obtain ⟨χ, hχ, hχbound⟩ := hbound N P hP
  refine ⟨χ, hχ, fun q => ?_⟩
  simpa only [mul_assoc] using abs_realCount_le_of_orthants P χ
    (C * upperGrowth d N) hχbound q

theorem main_upper_bound_asymptotic : AsymptoticUpperBound := by
  intro d hd
  obtain ⟨C, hC, N₀, hN₀, hbound⟩ := Tusnady.main_upper_bound_asymptotic d hd
  refine ⟨(2 : ℝ)^d * C, mul_pos (by positivity) hC, N₀, hN₀, ?_⟩
  intro N hN
  calc
    worstDiscrepancy d N ≤ (2 : ℝ)^d * Tusnady.worstDiscrepancy d N :=
      worstDiscrepancy_le_orthant (by omega) N
    _ ≤ (2 : ℝ)^d * (C * targetGrowth d N) :=
      mul_le_mul_of_nonneg_left (hbound N hN) (by positivity)
    _ = _ := by ring

theorem main_sharp_order : SharpOrder := by
  intro d hd
  obtain ⟨c, C, hc, hC, N₀, hN₀, hbound⟩ := Tusnady.main_sharp_order d hd
  refine ⟨c, (2 : ℝ)^d * C, hc, mul_pos (by positivity) hC, N₀, hN₀, ?_⟩
  intro N hN
  constructor
  · exact (hbound N hN).1.trans (orthant_worstDiscrepancy_le (by omega) N)
  · calc
      worstDiscrepancy d N ≤ (2 : ℝ)^d * Tusnady.worstDiscrepancy d N :=
        worstDiscrepancy_le_orthant (by omega) N
      _ ≤ (2 : ℝ)^d * (C * targetGrowth d N) :=
        mul_le_mul_of_nonneg_left (hbound N hN).2 (by positivity)
      _ = _ := by ring

theorem worstDiscrepancy_nonneg (hd : 0 < d) (N : ℕ) : 0 ≤ worstDiscrepancy d N :=
  (Tusnady.worstDiscrepancy_nonneg hd N).trans (orthant_worstDiscrepancy_le hd N)

/-- The two range classes have the same worst-case order in every positive
dimension, independently of any logarithmic upper or lower theorem. -/
theorem worstDiscrepancy_isTheta_orthant {d : ℕ} (hd : 0 < d) :
    Asymptotics.IsTheta Filter.atTop (worstDiscrepancy d) (Tusnady.worstDiscrepancy d) := by
  constructor
  · apply Asymptotics.IsBigO.of_bound ((2 : ℝ)^d)
    exact Filter.Eventually.of_forall fun N => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (worstDiscrepancy_nonneg hd N),
        abs_of_nonneg (Tusnady.worstDiscrepancy_nonneg hd N)] using
        worstDiscrepancy_le_orthant hd N
  · apply Asymptotics.IsBigO.of_bound 1
    exact Filter.Eventually.of_forall fun N => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (worstDiscrepancy_nonneg hd N),
        abs_of_nonneg (Tusnady.worstDiscrepancy_nonneg hd N), one_mul] using
        orthant_worstDiscrepancy_le hd N

theorem main_sharp_order_isTheta {d : ℕ} (hd : 3 ≤ d) :
    Asymptotics.IsTheta Filter.atTop (worstDiscrepancy d) (targetGrowth d) :=
  (worstDiscrepancy_isTheta_orthant (by omega)).trans (Tusnady.main_sharp_order_isTheta hd)

end Tusnady.Boxes
