import Tusnady.PlanarWei.Coordinates
import Wei.R56Audit.Parameters

/-!
# Wei's planar lower bound in the existing discrepancy definitions

The imported theorem is Zhewei Wei's fixed MIT software proof, not a new
literature assumption. Its integer base is chosen once before the sample size.
This file changes log base and transports the exact deterministic witness.
-/
noncomputable section
namespace Tusnady.PlanarWei

/-- Conversion of Wei's fixed base-dependent constant to natural logarithms. -/
def naturalLogConstant (b : ℕ) : ℝ :=
  R56Audit.cA b / (Real.log 2) ^ (3 / 2 : ℝ)

lemma naturalLogConstant_pos {b : ℕ} (hb : 2 ≤ b) : 0 < naturalLogConstant b :=
  div_pos (R56Audit.cA_pos hb) (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _)

lemma logb_growth_eq (b N : ℕ) (hN : 1 ≤ N) :
    R56Audit.cA b * Real.logb 2 (N : ℝ) ^ (3 / 2 : ℝ) =
      naturalLogConstant b * targetGrowth 2 N := by
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  change R56Audit.cA b * Real.logb 2 (N : ℝ) ^ (3 / 2 : ℝ) =
    naturalLogConstant b * (Real.log (N : ℝ)) ^ ((2 : ℝ) - 1/2)
  rw [show (2 : ℝ)-1/2 = 3/2 by norm_num, Real.logb,
    Real.div_rpow hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le]
  unfold naturalLogConstant
  ring

/-- Every positive cardinality has an injective planar witness. One positive
constant is chosen before N and works for all real ±1 colorings. -/
theorem planar_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      c * targetGrowth 2 N ≤ worstDiscrepancy 2 N := by
  obtain ⟨b, hb1, hb2⟩ := R56Audit.exists_base_of_15 1
  have hb : 49 ≤ b := R56Audit.base_ge_49 one_pos hb1
  refine ⟨naturalLogConstant b, naturalLogConstant_pos (by omega), fun N hN => ?_⟩
  obtain ⟨P, hPinj, hPcube, hPdisc⟩ := R56Audit.exists_points one_pos hb1 hb2 hN
  have hpoint := pointDiscrepancy_ge_of_units_supNorm P hPcube
    (R56Audit.cA b * Real.logb 2 (N : ℝ) ^ (3 / 2 : ℝ)) hPdisc
  rw [logb_growth_eq b N hN] at hpoint
  exact hpoint.trans (pointDiscrepancy_le_worst _ (injective_points hPinj))

end Tusnady.PlanarWei
