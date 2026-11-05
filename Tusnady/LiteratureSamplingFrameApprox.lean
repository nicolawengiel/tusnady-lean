import Tusnady.LiteratureSamplingNormApprox
import Tusnady.FrameBasic

/-! Actual finite vectors obtained from the preliminary unweighted sample. -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace Tusnady.LiteratureSampling

def nodeVector {X : Type*} {D m : ℕ} (u : Fin D → X → ℝ) (ξ : Fin m → X)
    (j : Fin m) : Frame.Space D :=
  WithLp.toLp 2 (fun i => u i (ξ j) / Real.sqrt m)

lemma nodeVector_norm_sq {X : Type*} {D m : ℕ} (u : Fin D → X → ℝ)
    (ξ : Fin m → X) (hm : 0 < m) (j : Fin m) :
    ‖nodeVector u ξ j‖ ^ 2 = (∑ i, u i (ξ j) ^ 2) / (m : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  change (∑ i, (u i (ξ j) / Real.sqrt m) ^ 2) = _
  simp only [div_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)]
  rw [Finset.sum_div]

lemma inner_nodeVector {X : Type*} {D m : ℕ} (u : Fin D → X → ℝ)
    (ξ : Fin m → X) (w : Frame.Space D) (j : Fin m) :
    inner ℝ w (nodeVector u ξ j) = (∑ i, w i * u i (ξ j)) / Real.sqrt m := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply', conj_trivial]
  change (∑ i, w i * (u i (ξ j) / Real.sqrt m)) = _
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma nodeVector_energy {X : Type*} {D m : ℕ} (u : Fin D → X → ℝ)
    (ξ : Fin m → X) (hm : 0 < m) (S : Finset (Fin m)) (w : Frame.Space D) :
    Frame.energy (nodeVector u ξ) S w =
      (1 / (m : ℝ)) * ∑ j ∈ S, (∑ i, w i * u i (ξ j)) ^ 2 := by
  simp only [Frame.energy, inner_nodeVector, div_pow,
    Real.sq_sqrt (show (0 : ℝ) ≤ m by positivity)]
  rw [← Finset.sum_div]
  ring

theorem exists_finite_frame_approximation {X : Type*} [MeasurableSpace X] {D : ℕ}
    (μ : Measure X) [IsProbabilityMeasure μ] (u : Fin D → X → ℝ)
    (hD : 0 < D) (humeas : ∀ i, Measurable (u i))
    (hint : ∀ i k, Integrable (fun x => u i x * u k x) μ)
    (horth : ∀ i k, (∫ x, u i x * u k x ∂μ) = if i = k then 1 else 0)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ)) (minimum : ℕ) :
    ∃ m : ℕ, 0 < m ∧ minimum ≤ m ∧ ∃ ξ : Fin m → X,
      (∀ j, ‖nodeVector u ξ j‖ ^ 2 ≤ (D : ℝ) / m) ∧
      (∀ w : Frame.Space D,
        (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ Frame.energy (nodeVector u ξ) Finset.univ w ∧
        Frame.energy (nodeVector u ξ) Finset.univ w ≤ (3 / 2 : ℝ) * ‖w‖ ^ 2) := by
  obtain ⟨m, hm, hmin, ξ, hξ⟩ := exists_finite_norm_approximation μ u hD humeas hint
    horth hE minimum
  refine ⟨m, hm, hmin, ξ, ?_, ?_⟩
  · intro j
    rw [nodeVector_norm_sq u ξ hm]
    exact div_le_div_of_nonneg_right (by simpa only [sq_abs] using hE (ξ j))
      (by positivity)
  · intro w
    have he := hξ (fun i => w i)
    have hn : ‖w‖ ^ 2 = ∑ i, w i ^ 2 := by
      simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    rw [nodeVector_energy u ξ hm, hn]
    simpa using he

end Tusnady.LiteratureSampling
