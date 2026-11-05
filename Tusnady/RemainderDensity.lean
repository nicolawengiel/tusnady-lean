import Tusnady.CellContinuity
import Tusnady.RemainderTheorem

/-! # Actual mean-square remainder density for mixed sampling

The finite nonnegative continuous energy density has integral exactly
equal to the actual product-uniform expected squared remainder norm.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Tusnady.Witness

theorem boxPrimitive_high_sq_integrable (d H h : ℕ) (f : Lp ℝ 2 (Haar.cubeMeasure d)) :
    Integrable (fun p => boxPrimitive (Haar.highProjection d H h f) p ^ 2)
      (Haar.cubeMeasure d) := by
  have hi := (Lp.memLp (Haar.primitiveCLM d (Haar.highProjection d H h f))).integrable_sq
  apply hi.congr
  filter_upwards [Haar.primitiveCLM_ae (Haar.highProjection d H h f)] with p hp
  rw [hp]

theorem cubicEnergyDensity_integrable (j : Fin d) (theta : ℝ) :
    Integrable (cubicEnergyDensity (h := h) j theta) (Haar.cubeMeasure d) :=
  integrable_finset_sum Finset.univ (fun G _ =>
    (boxPrimitive_high_sq_integrable d (h+3*d) h (cellL2Vector G)).const_mul _)

/-- Exact (4.7): spatial integral and coefficient expectation agree for
the actual density and actual cubic L² remainder. -/
theorem integral_cubicEnergyDensity (j : Fin d) (theta : ℝ) :
    (∫ p, cubicEnergyDensity (h := h) j theta p ∂Haar.cubeMeasure d) =
      ∫ u, ‖Haar.primitiveHighCLM d (h+3*d) h (cubicTestL2 j theta u)‖ ^ 2
        ∂UniformMonomial.cubeLaw (Shell d h) := by
  rw [expected_cubic_operator_sq]
  unfold cubicEnergyDensity
  rw [integral_finset_sum Finset.univ (fun G _ =>
    (boxPrimitive_high_sq_integrable d (h+3*d) h (cellL2Vector G)).const_mul _)]
  apply Finset.sum_congr rfl
  intro G _
  rw [integral_const_mul, ← Haar.primitiveHighCLM_norm_sq]

/-- The actual scalar error-density input used by the mixed sampler.
Its nonnegativity, continuity and integral estimate are all conclusions. -/
theorem cubicEnergyDensity_facts (d h : ℕ) (hd : 2 ≤ d)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ RemainderParameters.threshold d) :
    let j : Fin d := ⟨0,by omega⟩
    let w := cubicEnergyDensity (h := h) j (RemainderParameters.theta d h t)
    (∀ p, 0 ≤ w p) ∧ ContinuousOn w (UnitCube d) ∧ Integrable w (Haar.cubeMeasure d) ∧
      (∫ p, w p ∂Haar.cubeMeasure d) ≤
        remainderConstant d * RemainderParameters.lambda d h t ^ 2 *
          ((h : ℝ) + 1) ^ (d - 1) * DyadicFunctions.dyadicLength h ^ 2 *
            (RemainderParameters.theta d h t ^ 4 + RemainderParameters.lambda d h t ^ 4) := by
  dsimp only
  refine ⟨cubicEnergyDensity_nonneg _ _, cubicEnergyDensity_continuousOn (by omega) _ _,
    cubicEnergyDensity_integrable _ _, ?_⟩
  rw [integral_cubicEnergyDensity]
  exact expected_actual_cubic_remainder_sq d h hd ht htt

end Tusnady.Witness
