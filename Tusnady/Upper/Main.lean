import Tusnady.Upper.Ehrhard.VerticalFoldMonotonicity
import Tusnady.Upper.NikolovSmallRadiusReduction

/-!
# Nikolov's upper bound, with all analytic dependencies proved

The proof uses the conservative universal signing factor 1000.  Its Gaussian
fold monotonicity is proved in `VerticalFoldMonotonicity`; no literature
assumption, additional axiom or development placeholder is used here.
The existing discrepancy definitions and lower-bound theorem are unchanged.
-/
noncomputable section
namespace Tusnady
open Upper OAI.GaussianPropeller

/-- For each d ≥ 2 one positive dimension-only constant works for every N. -/
theorem main_upper_bound : HigherDimensionalUpperBound :=
  upperBound_of_smallGaussianFoldMonotonicity small_gaussian_fold_monotonicity

/-- One fixed real ±1 coloring controls every closed lower orthant at once. -/
theorem main_upper_bound_real_colorings : ColoringUpperBound :=
  upper_iff_coloringUpperBound.mp main_upper_bound

/-- The usual asymptotic bound with log N, with no unproved literature input. -/
theorem main_upper_bound_asymptotic : AsymptoticUpperBound :=
  upperBound_implies_asymptotic main_upper_bound

/-- The proved upper bound and the preserved unconditional lower theorem give
the sharp two-sided growth for every fixed dimension d ≥ 3. -/
theorem main_sharp_order : SharpHigherDimensionalOrder :=
  sharpOrder_of_upperBound main_upper_bound

theorem main_sharp_order_isTheta {d : ℕ} (hd : 3 ≤ d) :
    Asymptotics.IsTheta Filter.atTop (worstDiscrepancy d) (targetGrowth d) :=
  isTheta_of_upperBound main_upper_bound hd

/-- The explicit admissible constant is independent of N and of the point set:
`1000 * (3/log 2)^s * sqrt(2*(s+4))`, where the full dimension is s+1. -/
theorem main_upper_bound_explicit_constant (s : ℕ) (hs : 1 ≤ s) (N : ℕ) :
    worstDiscrepancy (s+1) N ≤ smallRadiusNikolovConstant s * upperGrowth (s+1) N := by
  by_cases hN : N = 0
  · subst N
    rw [worstDiscrepancy_zero (by omega)]
    exact mul_nonneg (smallRadiusNikolovConstant_pos s).le (upperGrowth_nonneg _ _)
  · apply (worstDiscrepancy_le_iff_real_colorings (by omega) N _).mpr
    intro P _
    exact orthant_coloring_of_smallGaussianFoldMonotonicity small_gaussian_fold_monotonicity
      (Nat.pos_of_ne_zero hN) P

theorem main_upper_bound_real_colorings_explicit_constant
    (s : ℕ) (hs : 1 ≤ s) (N : ℕ) (P : Fin N → Point (s+1)) (hP : Function.Injective P) :
    ∃ χ : Fin N → ℝ, IsSignColoring χ ∧ ∀ x : Point (s+1),
      |realAnchoredCount P χ x| ≤ smallRadiusNikolovConstant s * upperGrowth (s+1) N := by
  apply (pointDiscrepancy_le_iff_real_colorings P _).mp
  exact (pointDiscrepancy_le_worst P hP).trans (main_upper_bound_explicit_constant s hs N)

end Tusnady
