import Tusnady.Upper.Ehrhard.Symmetrization
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Closedness of Gaussian Ehrhard symmetrization

For a nonempty closed input, the section mass is a limit of continuous Gaussian
integrals of `exp(-N * distance(append(y,t), K))`, each of which dominates the
section mass.  Dominated convergence proves the limit; the continuous upper
approximations prove upper semicontinuity.  The empty set is handled separately.
No compactness, convexity, Gaussian axiom or fold premise is needed here.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology

namespace OAI.GaussianPropeller.Symmetrization
open Quantile GaussianSections

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))

private def distancePenalty (K : Set E') (N : ℕ) (y : E) (t : ℝ) : ℝ :=
  Real.exp (-(N : ℝ) * infDist (append y t) K)

private theorem distancePenalty_pos (K : Set E') (N : ℕ) (y : E) (t : ℝ) :
    0 < distancePenalty K N y t := Real.exp_pos _

private theorem distancePenalty_le_one (K : Set E') (N : ℕ) (y : E) (t : ℝ) :
    distancePenalty K N y t ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hd : 0 ≤ infDist (append y t) K := infDist_nonneg
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

private theorem continuous_distancePenalty_parameter (K : Set E') (N : ℕ) (t : ℝ) :
    Continuous (fun y : E => distancePenalty K N y t) :=
  Real.continuous_exp.comp (continuous_const.mul ((continuous_infDist_pt K).comp
    (continuous_append.comp (continuous_id.prodMk continuous_const))))

private theorem continuous_distancePenalty_scalar (K : Set E') (N : ℕ) (y : E) :
    Continuous (distancePenalty K N y) :=
  Real.continuous_exp.comp (continuous_const.mul ((continuous_infDist_pt K).comp
    (continuous_append.comp (continuous_const.prodMk continuous_id))))

private theorem integrable_distancePenalty (K : Set E') (N : ℕ) (y : E) :
    Integrable (distancePenalty K N y) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_distancePenalty_scalar K N y).aestronglyMeasurable
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_pos (distancePenalty_pos K N y t)]
    exact distancePenalty_le_one K N y t)

private def penaltyMass (K : Set E') (N : ℕ) (y : E) : ℝ :=
  ∫ t, distancePenalty K N y t ∂gaussianReal 0 1

private theorem continuous_penaltyMass (K : Set E') (N : ℕ) : Continuous (penaltyMass K N) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => (1 : ℝ))
  · intro y
    exact (continuous_distancePenalty_scalar K N y).aestronglyMeasurable
  · intro y
    exact ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (distancePenalty_pos K N y t)]
      exact distancePenalty_le_one K N y t)
  · exact integrable_const _
  · exact ae_of_all _ (continuous_distancePenalty_parameter K N)

private theorem distancePenalty_tendsto (K : Set E') (hK : IsClosed K) (hne : K.Nonempty)
    (y : E) (t : ℝ) :
    Tendsto (fun N : ℕ => distancePenalty K N y t) atTop
      (𝓝 ((verticalSection K y).indicator (fun _ => (1 : ℝ)) t)) := by
  by_cases ht : append y t ∈ K
  · have hd := infDist_zero_of_mem ht
    rw [indicator_of_mem (show t ∈ verticalSection K y from ht)]
    simp only [distancePenalty, hd, mul_zero, Real.exp_zero]
    exact tendsto_const_nhds
  · have hd : 0 < infDist (append y t) K := (hK.notMem_iff_infDist_pos hne).1 ht
    have hN : Tendsto (fun N : ℕ => (N : ℝ) * infDist (append y t) K) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const' hd
    rw [indicator_of_notMem (show t ∉ verticalSection K y from ht)]
    simpa only [distancePenalty, Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hN

private theorem penaltyMass_tendsto (K : Set E') (hK : IsClosed K) (hne : K.Nonempty) (y : E) :
    Tendsto (fun N : ℕ => penaltyMass K N y) atTop (𝓝 (sectionMass K y)) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := gaussianReal 0 1)
    (bound := fun _ : ℝ => (1 : ℝ))
    (F := fun N : ℕ => distancePenalty K N y)
    (f := (verticalSection K y).indicator (fun _ => (1 : ℝ)))
    (fun N => (continuous_distancePenalty_scalar K N y).aestronglyMeasurable)
    (integrable_const _) (fun N => ae_of_all _ (fun t => by
      rw [Real.norm_eq_abs, abs_of_pos (distancePenalty_pos K N y t)]
      exact distancePenalty_le_one K N y t))
    (ae_of_all _ (distancePenalty_tendsto K hK hne y))
  convert hlim using 1
  · rfl
  · rw [integral_indicator (measurableSet_verticalSection hK.measurableSet y), setIntegral_const]
    simp [sectionMass]

private theorem sectionMass_le_penaltyMass (K : Set E') (hK : IsClosed K) (N : ℕ) (y : E) :
    sectionMass K y ≤ penaltyMass K N y := by
  have hS := measurableSet_verticalSection hK.measurableSet y
  have hrep : sectionMass K y =
      ∫ t, (verticalSection K y).indicator (fun _ => (1 : ℝ)) t ∂gaussianReal 0 1 := by
    rw [integral_indicator hS, setIntegral_const]
    simp [sectionMass]
  rw [hrep]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hS) (integrable_distancePenalty K N y)
  intro t
  by_cases ht : t ∈ verticalSection K y
  · rw [indicator_of_mem ht]
    have hd := infDist_zero_of_mem (show append y t ∈ K from ht)
    simp [distancePenalty, hd]
  · rw [indicator_of_notMem ht]
    exact (distancePenalty_pos K N y t).le

/-- Actual upper semicontinuity of closed-set Gaussian section probabilities. -/
theorem upperSemicontinuous_sectionMass (K : Set E') (hK : IsClosed K) :
    UpperSemicontinuous (sectionMass K) := by
  by_cases hne : K.Nonempty
  · intro y a ha
    obtain ⟨N, hN⟩ := ((penaltyMass_tendsto K hK hne y).eventually (Iio_mem_nhds ha)).exists
    have he := (continuous_penaltyMass K N).continuousAt (Iio_mem_nhds hN)
    filter_upwards [he] with z hz
    exact (sectionMass_le_penaltyMass K hK N z).trans_lt hz
  · have hzero : sectionMass K = fun _ : E => (0 : ℝ) := by
      funext y
      simp [sectionMass, verticalSection, Set.not_nonempty_iff_eq_empty.mp hne]
    rw [hzero]
    exact continuous_const.upperSemicontinuous

/-- Gaussian symmetrization of every closed set is closed. -/
theorem isClosed_symmetrization (K : Set E') (hK : IsClosed K) :
    IsClosed (symmetrization K) := by
  have hp := (upperSemicontinuous_sectionMass K hK).comp continuous_front
  have hq : UpperSemicontinuous (fun z : E' => -Φ (last z)) :=
    (continuous_Φ.comp (continuous_last (k := k))).neg.upperSemicontinuous
  have hc := (hp.add hq).isClosed_preimage (0 : ℝ)
  convert hc using 1
  ext z
  simp only [symmetrization, mem_setOf_eq, mem_preimage, mem_Ici, Function.comp_def, Pi.add_apply]
  constructor <;> intro hz <;> linarith

end OAI.GaussianPropeller.Symmetrization
