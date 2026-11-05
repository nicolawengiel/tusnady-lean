import Tusnady.FullConcreteResponse
import Tusnady.RemainderRelative
import Tusnady.ResponseScale
import Tusnady.FiniteReindex

/-! # Cancellation of the actual sampled-response RMS scale

The sample count, target scale and shell volume remain actual quantities.
The final relative-error constant depends only on dimension and the fixed
literature sampling constants, never on depth or the selected points.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Tusnady.Witness

def shapeLowerResponseConstant (d : ℕ) : ℝ := 1 / ((3 : ℝ) * d) ^ (d - 1)

theorem shapeLowerResponseConstant_pos {d : ℕ} (hd : 1 ≤ d) :
    0 < shapeLowerResponseConstant d := by
  unfold shapeLowerResponseConstant
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  positivity

theorem shellVolume_mul_card_shell (d h : ℕ) :
    shellVolume h * Fintype.card (Shell d h) = (Fintype.card (Dyadic.Shape d h) : ℝ) := by
  rw [card_shell]
  push_cast
  unfold shellVolume
  field_simp

theorem shape_scale_le_volume_card (d h : ℕ) (hd : 1 ≤ d) (hh : 3 ∣ h) :
    shapeLowerResponseConstant d * ((h : ℝ) + 1) ^ (d - 1) ≤
      shellVolume h * Fintype.card (Shell d h) := by
  rw [shellVolume_mul_card_shell]
  exact card_shape_lower_dim d h hd hh

theorem shell_card_pos (d h : ℕ) (hd : 1 ≤ d) (hh : 3 ∣ h) : 0 < Fintype.card (Shell d h) := by
  have hshape := shape_scale_le_volume_card d h hd hh
  have hp : 0 < shapeLowerResponseConstant d * ((h : ℝ) + 1) ^ (d - 1) := by
    exact mul_pos (shapeLowerResponseConstant_pos hd) (by positivity)
  have hM : 0 < (Fintype.card (Shell d h) : ℝ) :=
    (mul_pos_iff_of_pos_left (shellVolume_pos h)).mp (hp.trans_le hshape)
  exact_mod_cast hM

def responseRmsConstant (d : ℕ) (c C₃ : ℝ) : ℝ :=
  Real.sqrt (128 * C₃ * remainderConstant d / (gamma d * c * shapeLowerResponseConstant d))

theorem responseRmsConstant_pos {d : ℕ} (hd : 2 ≤ d) {c C₃ : ℝ} (hc : 0 < c) (hC : 0 < C₃) :
    0 < responseRmsConstant d c C₃ := by
  unfold responseRmsConstant
  exact Real.sqrt_pos.mpr (div_pos
    (mul_pos (mul_pos (by norm_num) hC) (remainderConstant_pos (by omega)))
    (mul_pos (mul_pos (gamma_pos d) hc) (shapeLowerResponseConstant_pos (by omega))))

theorem response_error_scale_core (γ c L m v M cK X θ σ R C₃ E : ℝ)
    (hγ : 0 < γ) (hc : 0 < c) (hL : 0 < L) (_hv : 0 ≤ v)
    (hcK : 0 < cK) (_hθ : 0 ≤ θ) (hR : 0 ≤ R) (hC : 0 ≤ C₃) (hm : 0 ≤ m)
    (hσ : σ ^ 2 = (γ * v * c) * (m / L)) (hshape : cK * X ≤ v * M)
    (hE : E ≤ (m * C₃ / L) * R * θ ^ 2 * X * v ^ 2 * (θ ^ 4 + θ ^ 4)) :
    E ≤ ((Real.sqrt (128 * C₃ * R / (γ * c * cK)) * θ ^ 2) * (σ * v * θ / 8)) ^ 2 * M := by
  let B := 128 * C₃ * R / (γ * c * cK)
  let T := (2 * m * C₃ * R / L) * θ ^ 6 * v ^ 2 / cK
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hmultiply := mul_le_mul_of_nonneg_left hshape hT
  have hleft : (m * C₃ / L) * R * θ ^ 2 * X * v ^ 2 * (θ ^ 4 + θ ^ 4) = T * (cK * X) := by
    dsimp [T]
    field_simp
    ring
  have hright : ((Real.sqrt (128 * C₃ * R / (γ * c * cK)) * θ ^ 2) * (σ * v * θ / 8)) ^ 2 * M =
      T * (v * M) := by
    change ((Real.sqrt B * θ ^ 2) * (σ * v * θ / 8)) ^ 2 * M = _
    simp only [mul_pow, div_pow, Real.sq_sqrt hB, hσ]
    dsimp [B, T]
    field_simp
    ring
  rw [hleft] at hE
  rw [hright]
  exact hE.trans hmultiply

end Tusnady.Witness

namespace Tusnady.SamplingSpace.ConcreteSample
open Tusnady.Witness Tusnady.RemainderParameters
variable {d h m : ℕ} {c L : ℝ}

def minimalResponseScale (A : ConcreteSample d h m c L) (θ : ℝ) : ℝ :=
  A.targetScale * shellVolume h * θ / 8

theorem minimalResponseScale_pos (A : ConcreteSample d h m c L) {θ : ℝ} (hθ : 0 < θ) :
    0 < A.minimalResponseScale θ := by
  unfold minimalResponseScale
  exact div_pos (mul_pos (mul_pos A.targetScale_pos (shellVolume_pos h)) hθ) (by norm_num)

theorem responseWeights_lower (A : ConcreteSample d h m c L) (hd : 2 ≤ d)
    (j : Fin d) {t : ℝ} (ht : 0 ≤ t) (htt : t ≤ threshold d) (R : Shell d h) :
    A.minimalResponseScale (theta d h t) ≤ A.responseWeights j (theta d h t) R := by
  have hcoef := (linearCoefficient_bounds j (theta_nonneg d h ht)
    (parameter_block_budget d h hd j ht htt) R).1
  unfold minimalResponseScale responseWeights
  nlinarith [mul_le_mul_of_nonneg_left hcoef (mul_pos A.targetScale_pos (shellVolume_pos h)).le]

def responseErrorRatio (d h : ℕ) (c C₃ t : ℝ) : ℝ :=
  responseRmsConstant d c C₃ * t ^ 2 / ((h : ℝ) + 1) ^ (d - 2)

theorem responseErrorRatio_eq_theta (d h : ℕ) (c C₃ t : ℝ) :
    responseErrorRatio d h c C₃ t = responseRmsConstant d c C₃ * theta d h t ^ 2 := by
  rw [responseErrorRatio, theta_sq]
  ring

theorem response_error_relative_bound (A : ConcreteSample d h m c L)
    (hd : 2 ≤ d) (hh : 3 ∣ h) {C₃ t : ℝ} (hC₃ : 0 < C₃)
    (ht : 0 ≤ t) (htt : t ≤ threshold d)
    (herror : (∫ u, ‖A.errorResponse (⟨0,by omega⟩ : Fin d) (theta d h t) u‖ ^ 2
      ∂UniformMonomial.cubeLaw (Shell d h)) ≤
        ((m : ℝ) * C₃ / L) *
          (∫ p, cubicEnergyDensity (h := h) (⟨0,by omega⟩ : Fin d) (theta d h t) p
            ∂Haar.cubeMeasure d)) :
    (∫ u, ‖A.errorResponse (⟨0,by omega⟩ : Fin d) (theta d h t) u‖ ^ 2
      ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      (responseErrorRatio d h c C₃ t * A.minimalResponseScale (theta d h t)) ^ 2 *
        Fintype.card (Shell d h) := by
  have hθ := theta_nonneg d h ht
  have hlam : RemainderParameters.lambda d h t ^ 2 ≤ theta d h t ^ 2 := by
    unfold RemainderParameters.lambda
    nlinarith [sq_nonneg (theta d h t)]
  have hfour : RemainderParameters.lambda d h t ^ 4 ≤ theta d h t ^ 4 := by
    apply pow_le_pow_left₀ (by unfold RemainderParameters.lambda; positivity)
    unfold RemainderParameters.lambda
    linarith
  have hbound := (cubicEnergyDensity_facts d h hd ht htt).2.2.2
  have hvolume : shellVolume h = DyadicFunctions.dyadicLength h := by
    unfold shellVolume DyadicFunctions.dyadicLength
    simp
  rw [← hvolume] at hbound
  have hmass : 0 ≤ (m : ℝ) * C₃ / L := by
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hC₃.le) A.bound_pos.le
  have hcombined := herror.trans (mul_le_mul_of_nonneg_left hbound hmass)
  have hE : (∫ u, ‖A.errorResponse (⟨0,by omega⟩ : Fin d) (theta d h t) u‖ ^ 2
      ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      ((m : ℝ) * C₃ / L) * remainderConstant d * theta d h t ^ 2 *
        ((h : ℝ) + 1) ^ (d - 1) * shellVolume h ^ 2 *
          (theta d h t ^ 4 + theta d h t ^ 4) := by
    apply hcombined.trans
    have hR := remainderConstant_pos (d := d) (by omega)
    calc
      _ ≤ ((m : ℝ) * C₃ / L) *
          (remainderConstant d * theta d h t ^ 2 * ((h : ℝ) + 1) ^ (d - 1) *
            shellVolume h ^ 2 * (theta d h t ^ 4 + theta d h t ^ 4)) := by
        apply mul_le_mul_of_nonneg_left _ hmass
        gcongr
      _ = _ := by ring
  have hcore := response_error_scale_core (gamma d) c L m (shellVolume h)
    (Fintype.card (Shell d h)) (shapeLowerResponseConstant d)
    (((h : ℝ) + 1) ^ (d - 1)) (theta d h t) A.targetScale (remainderConstant d) C₃ _
    (gamma_pos d) A.lower_pos A.bound_pos (shellVolume_pos h).le
    (shapeLowerResponseConstant_pos (by omega)) hθ (remainderConstant_pos (by omega)).le hC₃.le
    (Nat.cast_nonneg _) A.targetScale_sq (shape_scale_le_volume_card d h (by omega) hh) hE
  rw [responseErrorRatio_eq_theta]
  exact hcore

def responseStrengthConstant (d : ℕ) (c L t : ℝ) : ℝ :=
  ResponseScale.scaleConstant t (Real.sqrt (gamma d * c / L)) (shapeLowerResponseConstant d)

theorem responseStrengthConstant_pos (A : ConcreteSample d h m c L) (hd : 2 ≤ d)
    {t : ℝ} (ht : 0 < t) : 0 < responseStrengthConstant d c L t := by
  apply ResponseScale.scaleConstant_pos _ _ _ ht
  · exact Real.sqrt_pos.mpr (div_pos (mul_pos (gamma_pos d) A.lower_pos) A.bound_pos)
  · exact shapeLowerResponseConstant_pos (by omega)

theorem minimalResponseScale_times_card_lower (A : ConcreteSample d h m c L)
    (hd : 2 ≤ d) (hh : 3 ∣ h) {t : ℝ} (ht : 0 < t) :
    responseStrengthConstant d c L t * Real.rpow ((h : ℝ) + 1) ((d : ℝ) - 1 / 2) ≤
      A.minimalResponseScale (theta d h t) * Fintype.card (Shell d h) := by
  have hMlow : Fintype.card (Shell d h) ≤ m :=
    FiniteReindex.matrix_card_le_of_injective (A.responseMatrix (h+3*d))
      (A.responseMatrix_injective (h+3*d))
  have hmv : (Fintype.card (Dyadic.Shape d h) : ℝ) ≤ (m : ℝ) * shellVolume h := by
    rw [← shellVolume_mul_card_shell]
    have hmR : (Fintype.card (Shell d h) : ℝ) ≤ m := by exact_mod_cast hMlow
    exact (mul_le_mul_of_nonneg_left hmR (shellVolume_pos h).le).trans_eq (mul_comm _ _)
  have hsig : Real.sqrt (gamma d * c / L) *
      Real.sqrt (Fintype.card (Dyadic.Shape d h)) ≤ A.targetScale := by
    have hh := ResponseScale.targetScale_lower (gamma d) c L (shellVolume h) m
      (Fintype.card (Dyadic.Shape d h)) 1 (gamma_pos d).le A.lower_pos.le A.bound_pos
      (shellVolume_pos h).le (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by norm_num)
      (by simpa using hmv)
    simpa only [Real.sqrt_one, mul_one, targetScale] using hh
  have hK := card_shape_lower_dim d h (by omega) hh
  have hcσ : 0 < Real.sqrt (gamma d * c / L) :=
    Real.sqrt_pos.mpr (div_pos (mul_pos (gamma_pos d) A.lower_pos) A.bound_pos)
  apply ResponseScale.response_times_card_lower_dim d hd ((h : ℝ)+1) t
    (Real.sqrt (gamma d*c/L)) (shapeLowerResponseConstant d) (shellVolume h)
    (Fintype.card (Shell d h)) (Fintype.card (Dyadic.Shape d h)) A.targetScale
    (A.minimalResponseScale (theta d h t)) (by positivity) ht hcσ
    (shapeLowerResponseConstant_pos (by omega)) (shellVolume_pos h).le (Nat.cast_nonneg _)
    hK hsig
  · exact (shellVolume_mul_card_shell d h).ge
  · unfold minimalResponseScale theta
    apply le_of_eq
    ring

end Tusnady.SamplingSpace.ConcreteSample
