import Tusnady.ResponseErrorScale
import Tusnady.ConstructionSize
import Tusnady.ErrorEstimates

/-! # Actual hereditary-discrepancy depth construction

Main.pdf Proposition 7.2. Every point, response and Gaussian body is
constructed from the fixed named literature bundle. Error absorption
fixes the threshold only after all dimension-dependent constants.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady
open Tusnady.Witness Tusnady.SamplingSpace Tusnady.SamplingSpace.ConcreteSample
open Tusnady.RemainderParameters

theorem card_shell_polynomial_upper (d h : ℕ) (hd : 1 ≤ d) :
    (Fintype.card (Shell d h) : ℝ) ≤ ((h : ℝ) + 1) ^ (d - 1) * (2 : ℝ) ^ h := by
  rw [card_shell]
  push_cast
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  cases d with
  | zero => omega
  | succ k => exact_mod_cast Dyadic.card_shape_le k h

theorem concreteResponse_duality (A : ConcreteSample d h m c L) (hd : 0 < d)
    (j : Fin d) (theta : ℝ) (z : Shell d h → ℝ)
    (hz : ∀ x ∈ UnitCube d,
      |∑ i ∈ trace (fun k => (A.nodes k : Point d)) x,
        (A.responseMatrix (h+3*d)).mulVec z i| ≤
          2 * MatrixDiscrepancy.hereditary (incidenceMatrix (fun k => (A.nodes k : Point d))))
    (u : Shell d h → ℝ) (hu : u ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ))) :
    inner ℝ (WithLp.toLp 2 z : ShellCoefficients d h) (A.testResponse j theta u) ≤
      2 * MatrixDiscrepancy.hereditary (incidenceMatrix (fun k => (A.nodes k : Point d))) := by
  have huabs : ∀ R, |u R| ≤ 1 := fun R => abs_le.mpr ⟨hu.1 R, hu.2 R⟩
  have ht : 0 ≤ 2 * MatrixDiscrepancy.hereditary (incidenceMatrix (fun k => (A.nodes k : Point d))) :=
    mul_nonneg (by norm_num) (MatrixDiscrepancy.hereditary_nonneg _)
  cases d with
  | zero => omega
  | succ k => exact A.testResponse_weighted_duality j theta u z huabs _ ht hz

/-- Actual Proposition 7.2 and the cardinality needed by the final
logarithmic transfer. There is no unproved construction premise: the only
external inputs are the explicitly named genuine literature results. -/
theorem depth_construction_hereditary (literature : Literature.Assumptions)
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ hmin : ℕ,
      ∀ h : ℕ, 0 < h → 3 ∣ h → hmin ≤ h →
        ∃ n : ℕ, ∃ P : Fin n → Point d, Function.Injective P ∧
          (∀ i, P i ∈ OpenUnitCube d) ∧
          (n : ℝ) ≤ C * ((h : ℝ) + 1) ^ (d - 1) * (2 : ℝ) ^ h ∧
          c * Real.rpow ((h : ℝ) + 1) ((d : ℝ) - 1 / 2) ≤
            MatrixDiscrepancy.hereditary (incidenceMatrix P) := by
  obtain ⟨Cs, c0, Cerror, hCs, hc0, hCerror, hsamples⟩ :=
    remainder_response_construction literature.sampling
  let L : ℝ := 2 * (28 : ℝ) ^ d
  let t : ℝ := threshold d
  let Csize : ℝ := Cs * sizeUpperConstant d
  let kappa : ℝ := gaussianCoverEntropyRate * Csize
  let centropy : ℝ := gaussianRosenblattConstant kappa
  let cstrength : ℝ := responseStrengthConstant d c0 L t
  let Crho : ℝ := responseRmsConstant d c0 Cerror * t ^ 2
  have hL : 0 < L := by dsimp [L]; positivity
  have ht : 0 < t := threshold_pos (by omega)
  have hCsize : 0 < Csize := mul_pos hCs (sizeUpperConstant_pos (by omega))
  have hcentropy : 0 < centropy := gaussianRosenblattConstant_pos kappa
  have hstrength : 0 < cstrength := by
    apply ResponseScale.scaleConstant_pos _ _ _ ht
    · exact Real.sqrt_pos.mpr (div_pos (mul_pos (gamma_pos d) hc0) hL)
    · exact shapeLowerResponseConstant_pos (by omega)
  obtain ⟨hmin, _, _, hsmall⟩ := eventually_small_relative_error_on_shells hd
    (C := Crho) (c := centropy) hcentropy
  refine ⟨(centropy / 4) * cstrength, Csize,
    mul_pos (div_pos hcentropy (by norm_num)) hstrength, hCsize, hmin, ?_⟩
  intro h _hhpos hh hhmin
  let j : Fin d := ⟨0,by omega⟩
  obtain ⟨n, _hdim, hn, A, hPi, herror⟩ := hsamples d h (by omega) j (theta d h t)
  let P : Fin n → Point d := fun i => A.nodes i
  let rho := responseErrorRatio d h c0 Cerror t
  let smin := A.minimalResponseScale (theta d h t)
  have hPc : ∀ i, P i ∈ OpenUnitCube d := fun i =>
    samplingDomain_subset_OpenUnitCube (A.nodes i).property
  have hsize : (n : ℝ) ≤ Csize * Fintype.card (Shell d h) :=
    sample_count_shell_upper d h n (by omega) hh Cs hCs.le hn
  have hsmin : 0 < smin := A.minimalResponseScale_pos (theta_pos d h ht)
  have hrho : 0 ≤ rho := by
    unfold rho responseErrorRatio
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sq_nonneg _)) (by positivity)
  have hρsmall : rho ≤ centropy / 2 := by
    exact hsmall h hhmin
  have hError : (∫ u, ‖A.errorResponse j (theta d h t) u‖ ^ 2
      ∂UniformMonomial.cubeLaw (Shell d h)) ≤ (rho * smin) ^ 2 * Fintype.card (Shell d h) := by
    exact A.response_error_relative_bound (by omega) hh hCerror ht.le le_rfl herror
  have hobstruction := pointGaussianBody_obstruction_fintype literature
    (Witness.card_shell_pos d h (by omega) hh) P hPi hPc
    (A.responseMatrix (h+3*d)) (A.responseMatrix_injective _) (A.responseMatrix_row_sq_le_one _)
    Csize hsize (A.responseWeights j (theta d h t)) smin rho hsmin.le hrho
    (A.responseWeights_lower (by omega) j ht.le le_rfl)
    (A.testResponse j (theta d h t)) (A.errorResponse j (theta d h t))
    (A.errorResponse_continuous (by omega) j (theta d h t))
    (fun u _ => A.testResponse_decomposition j (theta d h t) u)
    (concreteResponse_duality A (by omega) j (theta d h t)) hError
  have habsorb := absorb_small_error hsmin.le (Nat.cast_nonneg (Fintype.card (Shell d h)))
    hρsmall hobstruction
  have hstrengthscale : cstrength * Real.rpow ((h : ℝ) + 1) ((d : ℝ) - 1 / 2) ≤
      smin * Fintype.card (Shell d h) :=
    A.minimalResponseScale_times_card_lower (by omega) hh ht
  refine ⟨n, P, hPi, hPc, ?_, ?_⟩
  · have hcard := mul_le_mul_of_nonneg_left (card_shell_polynomial_upper d h (by omega)) hCsize.le
    exact hsize.trans (by simpa only [mul_assoc] using hcard)
  · have hscaled := mul_le_mul_of_nonneg_left hstrengthscale
      (div_pos hcentropy (by norm_num : (0 : ℝ) < 4)).le
    calc
      _ = (centropy / 4) * (cstrength * Real.rpow ((h : ℝ) + 1) ((d : ℝ) - 1 / 2)) := by ring
      _ ≤ (centropy / 4) * (smin * Fintype.card (Shell d h)) := hscaled
      _ = (centropy / 4) * smin * Fintype.card (Shell d h) := by ring
      _ ≤ _ := habsorb

end Tusnady
