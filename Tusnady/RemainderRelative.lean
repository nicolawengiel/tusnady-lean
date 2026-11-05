import Tusnady.RemainderPhysical
import Tusnady.ShapeCounting

/-! # Relative mean-square error and the actual block budget

The modulation budget, quantitative linear lower bound and relative
error estimate are consequences of the actual parameter and shape count.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Tusnady.Witness
open Tusnady.RemainderParameters

theorem parameter_block_budget (d h : ℕ) (hd : 2 ≤ d) (j : Fin d)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) (a : BlockIndex h) :
    theta d h t ^ 2 * (Fintype.card (ShapesInBlock j a) : ℝ) ≤ (1 : ℝ) / 4 := by
  have hc : (Fintype.card (ShapesInBlock j a) : ℝ) ≤ ((h : ℝ) + 1) ^ (d - 2) := by
    cases d with
    | zero => omega
    | succ n =>
      cases n with
      | zero => omega
      | succ k => exact_mod_cast card_shapesInBlock_le k h j a
  have hp : 0 < ((h : ℝ) + 1) ^ (d - 2) := by positivity
  have thalf := htt.trans (threshold_le_half d)
  calc
    _ ≤ theta d h t ^ 2 * ((h : ℝ) + 1) ^ (d - 2) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
    _ = t ^ 2 := by rw [theta_sq, div_mul_cancel₀ _ hp.ne']
    _ ≤ _ := by nlinarith

theorem card_shape_lower_dim (d h : ℕ) (hd : 1 ≤ d) (hh : 3 ∣ h) :
    (1 / ((3 : ℝ) * d) ^ (d - 1)) * ((h : ℝ) + 1) ^ (d - 1) ≤
      (Fintype.card (Dyadic.Shape d h) : ℝ) := by
  cases d with
  | zero => omega
  | succ k => simpa only [Nat.cast_add, Nat.cast_one] using Dyadic.card_shape_lower k h hh

def linearEnergyLowerConstant (d : ℕ) : ℝ :=
  gamma d / (192 * ((3 : ℝ) * d) ^ (d - 1))

theorem linearEnergyLowerConstant_pos {d : ℕ} (hd : 1 ≤ d) : 0 < linearEnergyLowerConstant d := by
  unfold linearEnergyLowerConstant
  exact div_pos (gamma_pos d) (mul_pos (by norm_num)
    (pow_pos (mul_pos (by norm_num) (by exact_mod_cast (show 0 < d by omega))) _))

theorem expected_linearPrimitive_lower_parameter (d h : ℕ) (hd : 2 ≤ d)
    (hh : 3 ∣ h) (j : Fin d) {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    linearEnergyLowerConstant d * theta d h t ^ 2 * ((h : ℝ) + 1) ^ (d - 1) * shellVolume h ^ 2 ≤
      (∫ u, (∫ p, linearPrimitiveValue j (theta d h t) u p ^ 2 ∂Haar.cubeMeasure d)
        ∂UniformMonomial.cubeLaw (Shell d h)) := by
  have hlin := (expected_linearPrimitive_bounds j (theta_nonneg d h ht)
    (parameter_block_budget d h hd j ht htt)).1
  have hc := card_shape_lower_dim d h (by omega) hh
  have hp : 0 ≤ (gamma d / 192) * theta d h t ^ 2 * shellVolume h ^ 2 := by
    have hg := gamma_pos d
    positivity
  apply le_trans _ hlin
  have hm := mul_le_mul_of_nonneg_left hc hp
  convert hm using 1
  · unfold linearEnergyLowerConstant
    ring
  · ring

def relativeErrorConstant (d : ℕ) : ℝ :=
  2 * remainderConstant d / linearEnergyLowerConstant d

theorem relativeErrorConstant_pos {d : ℕ} (hd : 2 ≤ d) : 0 < relativeErrorConstant d := by
  unfold relativeErrorConstant
  exact div_pos (mul_pos (by norm_num) (remainderConstant_pos (by omega)))
    (linearEnergyLowerConstant_pos (by omega))

theorem expected_relative_cubic_remainder (d h : ℕ) (hd : 2 ≤ d) (hh : 3 ∣ h)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (∫ u, ‖Haar.primitiveHighCLM d (h+3*d) h
      (cubicTestL2 (⟨0,by omega⟩ : Fin d) (theta d h t) u)‖ ^ 2
        ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      relativeErrorConstant d * theta d h t ^ 4 *
        (∫ u, (∫ p, linearPrimitiveValue (⟨0,by omega⟩ : Fin d) (theta d h t) u p ^ 2
          ∂Haar.cubeMeasure d) ∂UniformMonomial.cubeLaw (Shell d h)) := by
  have hθ := theta_nonneg d h ht
  have hlam : 0 ≤ lambda d h t := by unfold lambda; positivity
  have hlamtheta : lambda d h t ≤ theta d h t := by unfold lambda; linarith
  have hsq := pow_le_pow_left₀ hlam hlamtheta 2
  have hfour := pow_le_pow_left₀ hlam hlamtheta 4
  have hupper := expected_actual_cubic_remainder_sq d h hd ht htt
  have hlower := expected_linearPrimitive_lower_parameter d h hd hh ⟨0,by omega⟩ ht htt
  have hA := linearEnergyLowerConstant_pos (d := d) (by omega)
  have hR := remainderConstant_pos (d := d) (by omega)
  have hvolume : shellVolume h = DyadicFunctions.dyadicLength h := by
    unfold shellVolume DyadicFunctions.dyadicLength
    simp
  rw [hvolume] at hlower
  have hrel : 0 ≤ relativeErrorConstant d * theta d h t ^ 4 := by
    exact mul_nonneg (relativeErrorConstant_pos hd).le (by positivity)
  apply hupper.trans
  calc
    _ ≤ remainderConstant d * theta d h t ^ 2 * ((h : ℝ) + 1) ^ (d - 1) *
        DyadicFunctions.dyadicLength h ^ 2 * (theta d h t ^ 4 + theta d h t ^ 4) := by
      gcongr
    _ = relativeErrorConstant d * theta d h t ^ 4 *
        (linearEnergyLowerConstant d * theta d h t ^ 2 * ((h : ℝ) + 1) ^ (d - 1) *
          DyadicFunctions.dyadicLength h ^ 2) := by
      unfold relativeErrorConstant
      field_simp [hA.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlower hrel

theorem expected_physical_remainder_sq (d h : ℕ) (hd : 2 ≤ d)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (∫ u, (∫ p, physicalRemainder (⟨0,by omega⟩ : Fin d) (theta d h t) u p ^ 2
      ∂Haar.cubeMeasure d) ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      remainderConstant d * lambda d h t ^ 2 * ((h : ℝ) + 1) ^ (d - 1) *
        DyadicFunctions.dyadicLength h ^ 2 * (theta d h t ^ 4 + lambda d h t ^ 4) := by
  have heq (u : Shell d h → ℝ) := cubic_norm_sq_eq_integral_physical (by omega : 0 < d)
    (⟨0,by omega⟩ : Fin d) (theta d h t) u
  simp_rw [← heq]
  exact expected_actual_cubic_remainder_sq d h hd ht htt

/-- The actual physical form of the relative inequality in Theorem 4.1. -/
theorem expected_relative_physical_remainder (d h : ℕ) (hd : 2 ≤ d) (hh : 3 ∣ h)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (∫ u, (∫ p, physicalRemainder (⟨0,by omega⟩ : Fin d) (theta d h t) u p ^ 2
      ∂Haar.cubeMeasure d) ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      relativeErrorConstant d * theta d h t ^ 4 *
        (∫ u, (∫ p, linearPrimitiveValue (⟨0,by omega⟩ : Fin d) (theta d h t) u p ^ 2
          ∂Haar.cubeMeasure d) ∂UniformMonomial.cubeLaw (Shell d h)) := by
  have heq (u : Shell d h → ℝ) := cubic_norm_sq_eq_integral_physical (by omega : 0 < d)
    (⟨0,by omega⟩ : Fin d) (theta d h t) u
  simp_rw [← heq]
  exact expected_relative_cubic_remainder d h hd hh ht htt

/-- Explicit relative root-mean-square scale. The only h-dependence is
`(h+1)^(-(d-2))`; in dimensions at least three it tends to zero. -/
theorem expected_relative_physical_remainder_decay (d h : ℕ) (hd : 2 ≤ d) (hh : 3 ∣ h)
    {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) :
    (∫ u, (∫ p, physicalRemainder (⟨0,by omega⟩ : Fin d) (theta d h t) u p ^ 2
      ∂Haar.cubeMeasure d) ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      (Real.sqrt (relativeErrorConstant d) * t ^ 2 / ((h : ℝ) + 1) ^ (d - 2)) ^ 2 *
        (∫ u, (∫ p, linearPrimitiveValue (⟨0,by omega⟩ : Fin d) (theta d h t) u p ^ 2
          ∂Haar.cubeMeasure d) ∂UniformMonomial.cubeLaw (Shell d h)) := by
  have heq : relativeErrorConstant d * theta d h t ^ 4 =
      (Real.sqrt (relativeErrorConstant d) * t ^ 2 / ((h : ℝ) + 1) ^ (d - 2)) ^ 2 := by
    rw [show theta d h t ^ 4 = (theta d h t ^ 2) ^ 2 by ring, theta_sq,
      div_pow, div_pow, mul_pow, Real.sq_sqrt (relativeErrorConstant_pos hd).le]
    ring
  rw [← heq]
  exact expected_relative_physical_remainder d h hd hh ht htt

end Tusnady.Witness
