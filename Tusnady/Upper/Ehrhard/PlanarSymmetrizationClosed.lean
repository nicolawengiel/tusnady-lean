import Tusnady.Upper.Ehrhard.PlanarSymmetrization

/-!
# Closedness of the planar Gaussian symmetrization

The horizontal Gaussian noise may have dimension zero.  Closedness of the
input suffices: continuous bounded distance penalties dominate the horizontal
section probability and converge to it by the actual dominated convergence
theorem.  No extra analytic or geometric hypothesis is assumed.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology

namespace OAI.GaussianPropeller.PlanarSymmetrization
open Quantile GaussianSections
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

private def horizontalPenalty (K : Set E') (N : ℕ) (t : ℝ) (y : E) : ℝ :=
  Real.exp (-(N : ℝ) * infDist (append y t) K)

private theorem horizontalPenalty_pos (K : Set E') (N : ℕ) (t : ℝ) (y : E) :
    0 < horizontalPenalty K N t y := Real.exp_pos _

private theorem horizontalPenalty_le_one (K : Set E') (N : ℕ) (t : ℝ) (y : E) :
    horizontalPenalty K N t y ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hd : 0 ≤ infDist (append y t) K := infDist_nonneg
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

private theorem continuous_horizontalPenalty_parameter (K : Set E') (N : ℕ) (y : E) :
    Continuous (fun t : ℝ => horizontalPenalty K N t y) :=
  Real.continuous_exp.comp (continuous_const.mul ((continuous_infDist_pt K).comp
    (continuous_append.comp (continuous_const.prodMk continuous_id))))

private theorem continuous_horizontalPenalty_noise (K : Set E') (N : ℕ) (t : ℝ) :
    Continuous (horizontalPenalty K N t) :=
  Real.continuous_exp.comp (continuous_const.mul ((continuous_infDist_pt K).comp
    (continuous_append.comp (continuous_id.prodMk continuous_const))))

private theorem integrable_horizontalPenalty (K : Set E') (N : ℕ) (t : ℝ) :
    Integrable (horizontalPenalty K N t) (gaussianMeasure (Fin k)) := by
  apply (integrable_const (1 : ℝ)).mono' (continuous_horizontalPenalty_noise K N t).aestronglyMeasurable
  exact ae_of_all _ (fun y => by
    rw [Real.norm_eq_abs, abs_of_pos (horizontalPenalty_pos K N t y)]
    exact horizontalPenalty_le_one K N t y)

private def horizontalPenaltyMass (K : Set E') (N : ℕ) (t : ℝ) : ℝ :=
  ∫ y, horizontalPenalty K N t y ∂gaussianMeasure (Fin k)

private theorem continuous_horizontalPenaltyMass (K : Set E') (N : ℕ) :
    Continuous (horizontalPenaltyMass K N) := by
  apply continuous_of_dominated (bound := fun _ : E => (1 : ℝ))
  · intro t
    exact (continuous_horizontalPenalty_noise K N t).aestronglyMeasurable
  · intro t
    exact ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (horizontalPenalty_pos K N t y)]
      exact horizontalPenalty_le_one K N t y)
  · exact integrable_const _
  · exact ae_of_all _ (continuous_horizontalPenalty_parameter K N)

private theorem horizontalPenalty_tendsto (K : Set E') (hK : IsClosed K) (hne : K.Nonempty)
    (t : ℝ) (y : E) :
    Tendsto (fun N : ℕ => horizontalPenalty K N t y) atTop
      (𝓝 ((horizontalSection K t).indicator (fun _ => (1 : ℝ)) y)) := by
  by_cases hy : append y t ∈ K
  · have hd := infDist_zero_of_mem hy
    rw [indicator_of_mem (show y ∈ horizontalSection K t from hy)]
    simp only [horizontalPenalty, hd, mul_zero, Real.exp_zero]
    exact tendsto_const_nhds
  · have hd : 0 < infDist (append y t) K := (hK.notMem_iff_infDist_pos hne).1 hy
    have hN : Tendsto (fun N : ℕ => (N : ℝ) * infDist (append y t) K) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const' hd
    rw [indicator_of_notMem (show y ∉ horizontalSection K t from hy)]
    simpa only [horizontalPenalty, Function.comp_def, neg_mul] using
      Real.tendsto_exp_neg_atTop_nhds_zero.comp hN

private theorem horizontalPenaltyMass_tendsto (K : Set E') (hK : IsClosed K) (hne : K.Nonempty) (t : ℝ) :
    Tendsto (fun N : ℕ => horizontalPenaltyMass K N t) atTop (𝓝 (horizontalMass K t)) := by
  have hlim := tendsto_integral_of_dominated_convergence (μ := gaussianMeasure (Fin k))
    (bound := fun _ : E => (1 : ℝ))
    (F := fun N : ℕ => horizontalPenalty K N t)
    (f := (horizontalSection K t).indicator (fun _ => (1 : ℝ)))
    (fun N => (continuous_horizontalPenalty_noise K N t).aestronglyMeasurable)
    (integrable_const _) (fun N => ae_of_all _ (fun y => by
      rw [Real.norm_eq_abs, abs_of_pos (horizontalPenalty_pos K N t y)]
      exact horizontalPenalty_le_one K N t y))
    (ae_of_all _ (horizontalPenalty_tendsto K hK hne t))
  convert hlim using 1
  · rfl
  · rw [integral_indicator (measurableSet_horizontalSection hK.measurableSet t), setIntegral_const]
    simp [horizontalMass]

private theorem horizontalMass_le_penaltyMass (K : Set E') (hK : IsClosed K) (N : ℕ) (t : ℝ) :
    horizontalMass K t ≤ horizontalPenaltyMass K N t := by
  have hS := measurableSet_horizontalSection hK.measurableSet t
  have hrep : horizontalMass K t =
      ∫ y, (horizontalSection K t).indicator (fun _ => (1 : ℝ)) y ∂gaussianMeasure (Fin k) := by
    rw [integral_indicator hS, setIntegral_const]
    simp [horizontalMass]
  rw [hrep]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hS) (integrable_horizontalPenalty K N t)
  intro y
  by_cases hy : y ∈ horizontalSection K t
  · rw [indicator_of_mem hy]
    have hd := infDist_zero_of_mem (show append y t ∈ K from hy)
    simp [horizontalPenalty, hd]
  · rw [indicator_of_notMem hy]
    exact (horizontalPenalty_pos K N t y).le

theorem upperSemicontinuous_horizontalMass (K : Set E') (hK : IsClosed K) :
    UpperSemicontinuous (horizontalMass K) := by
  by_cases hne : K.Nonempty
  · intro t a ha
    obtain ⟨N, hN⟩ := ((horizontalPenaltyMass_tendsto K hK hne t).eventually (Iio_mem_nhds ha)).exists
    have he := (continuous_horizontalPenaltyMass K N).continuousAt (Iio_mem_nhds hN)
    filter_upwards [he] with s hs
    exact (horizontalMass_le_penaltyMass K hK N s).trans_lt hs
  · have hzero : horizontalMass K = fun _ : ℝ => (0 : ℝ) := by
      funext t
      simp [horizontalMass, horizontalSection, Set.not_nonempty_iff_eq_empty.mp hne]
    rw [hzero]
    exact continuous_const.upperSemicontinuous

theorem isClosed_planarSymmetrization (K : Set E') (hK : IsClosed K) :
    IsClosed (planarSymmetrization K) := by
  have hp := (upperSemicontinuous_horizontalMass K hK).comp
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  have hq : UpperSemicontinuous (fun z : Plane => -Φ (z 0)) :=
    (continuous_Φ.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).neg.upperSemicontinuous
  have hc := (hp.add hq).isClosed_preimage (0 : ℝ)
  convert hc using 1
  ext z
  simp only [planarSymmetrization, mem_setOf_eq, mem_preimage, mem_Ici, Function.comp_def, Pi.add_apply]
  constructor <;> intro hz <;> linarith

end OAI.GaussianPropeller.PlanarSymmetrization
