import Tusnady.Upper.GaussianBody
import Tusnady.Upper.GaussianThreshold
import Tusnady.Upper.DyadicFactorization
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# A compact high-mass body for the prefix signing argument

The finite slab intersection may be unbounded.  Intersecting with a sufficiently
large Euclidean ball makes it compact, spending a separate, explicit tail
budget.  The row threshold is unchanged.  This removes any full-row-rank or
general-position premise from Nikolov's application of the convex-body theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace NNReal ENNReal
namespace Tusnady.Upper

/-- A finite probability measure on Euclidean space gives arbitrarily high mass
to a sufficiently large closed ball.  The chosen radius need not be uniform. -/
theorem probability_exists_large_closedBall {k : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin k))) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : ℝ, 0 < T ∧ 1 - δ ≤ μ.real (Metric.closedBall 0 T) := by
  obtain ⟨A, hAc, hAm⟩ := exists_isCompact_closure_measure_compl_lt μ
    (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  obtain ⟨R, hR⟩ := hAc.isBounded.exists_norm_le
  let T : ℝ := max R 1
  have hT : 0 < T := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : A ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) T := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hR z (subset_closure hz)).trans (le_max_left _ _)
  have htail : μ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) T)ᶜ ≤
      ENNReal.ofReal δ := (measure_mono (compl_subset_compl.mpr hsub)).trans hAm.le
  have hreal : μ.real (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) T)ᶜ ≤ δ := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top htail).trans_eq
      (ENNReal.toReal_ofReal hδ.le)
  rw [measureReal_compl Metric.isClosed_closedBall.measurableSet] at hreal
  simp only [probReal_univ] at hreal
  exact ⟨T, hT, by linarith⟩

/-- Squaring the chosen threshold gives exactly the exponent needed in the
Gaussian tail bound.  Positivity of the variance proxy handles zero rows too. -/
lemma gaussianThreshold_exponent (s N : ℕ) (hN : 0 < N) {B : ℝ} (hB : 0 < B) :
    -(B * Real.sqrt (2 * Real.log (gaussianTailScale s N)))^2 / (2*B^2) =
      -Real.log (gaussianTailScale s N) := by
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.log (gaussianTailScale s N) by
    exact mul_nonneg (by norm_num) (log_gaussianTailScale_pos s N hN).le)
  rw [mul_pow, hs]
  field_simp

/-- The genuine Gaussian slab body has the first half of the required error
budget.  There are `(N+1)^s` rows, including empty orthant traces. -/
theorem query_rowSlabs_mass {s N k : ℕ} (hN : 0 < N)
    (U : DyadicFactorization.Query s N → EuclideanSpace ℝ (Fin k))
    {B : ℝ} (hB : 0 < B) (hU : ∀ q, ‖U q‖ ≤ B) :
    1 - 1/(4*(N : ℝ)) ≤ (euclideanGaussian k).real
      (rowSlabs U (B * Real.sqrt (2 * Real.log (gaussianTailScale s N)))) := by
  have h := rowSlabs_mass U hB hU (gaussianThreshold_pos s N hN hB).le
  rw [gaussianThreshold_exponent s N hN hB, DyadicFactorization.query_card] at h
  have hcast : (((N+1)^s : ℕ) : ℝ) = ((N : ℝ)+1)^s := by push_cast; rfl
  rw [hcast] at h
  have heq : ((N : ℝ)+1)^s * (2 * Real.exp (-Real.log (gaussianTailScale s N))) =
      1/(4*(N : ℝ)) := by
    rw [← query_tail_union_budget s N hN]
    ring
  simpa only [heq] using h

/-- The compact convex origin-symmetric body required by the actual prefix
argument.  Its Gaussian mass is at least `1 - 1/(2N)`, while every row slab
retains exactly the threshold used in Nikolov's proof. -/
theorem exists_compact_query_body {s N k : ℕ} (hN : 0 < N)
    (U : DyadicFactorization.Query s N → EuclideanSpace ℝ (Fin k))
    {B : ℝ} (hB : 0 < B) (hU : ∀ q, ‖U q‖ ≤ B) :
    ∃ K : Set (EuclideanSpace ℝ (Fin k)),
      IsCompact K ∧ Convex ℝ K ∧ (∀ z ∈ K, -z ∈ K) ∧ (0 : EuclideanSpace ℝ (Fin k)) ∈ K ∧
      1 - 1/(2*(N : ℝ)) ≤ (euclideanGaussian k).real K ∧
      K ⊆ rowSlabs U (B * Real.sqrt (2 * Real.log (gaussianTailScale s N))) := by
  let R := B * Real.sqrt (2 * Real.log (gaussianTailScale s N))
  have hR : 0 < R := gaussianThreshold_pos s N hN hB
  have hδ : 0 < 1/(4*(N : ℝ)) := by positivity
  obtain ⟨T, hT, hball⟩ := probability_exists_large_closedBall (euclideanGaussian k) hδ
  let K := rowSlabs U R ∩ Metric.closedBall 0 T
  refine ⟨K, ?_, ?_, ?_, ?_, ?_, Set.inter_subset_left⟩
  · exact (isCompact_closedBall 0 T).inter_left (rowSlabs_closed U R)
  · exact (rowSlabs_convex U R).inter (convex_closedBall 0 T)
  · intro z hz
    refine ⟨rowSlabs_symmetric U R z hz.1, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_neg] using hz.2
  · exact ⟨rowSlabs_zero U hR.le, Metric.mem_closedBall_self hT.le⟩
  · have hm := query_rowSlabs_mass hN U hB hU
    have hi := probability_inter_lower (euclideanGaussian k) (rowSlabs U R)
      (Metric.closedBall 0 T) Metric.isClosed_closedBall.measurableSet
    change 1 - 1/(2*(N : ℝ)) ≤ (euclideanGaussian k).real
      (rowSlabs U R ∩ Metric.closedBall 0 T)
    have heq : 1/(2*(N : ℝ)) = 2*(1/(4*(N : ℝ))) := by ring
    rw [heq]
    dsimp [R] at hi ⊢
    linarith

end Tusnady.Upper
