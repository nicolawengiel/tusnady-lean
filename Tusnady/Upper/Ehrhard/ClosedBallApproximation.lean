import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# Compact exhaustion of a closed convex set by centered closed balls

The indicator convergence is eventually exact at every point, including all
boundary points. Probability convergence is proved by dominated convergence.
No isoperimetric or Gaussian literature statement is assumed.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology Pointwise
namespace OAI.GaussianPropeller.ClosedBallApproximation

variable {E : Type*} [NormedAddCommGroup E]

/-- The closed set K cut off at the natural radius n. -/
def ballApprox (K : Set E) (n : ℕ) : Set E := K ∩ Metric.closedBall 0 (n : ℝ)

lemma ballApprox_subset (K : Set E) (n : ℕ) : ballApprox K n ⊆ K := inter_subset_left

lemma ballApprox_mono (K : Set E) : Monotone (ballApprox K) := by
  intro m n hmn x hx
  exact ⟨hx.1, Metric.closedBall_subset_closedBall (by exact_mod_cast hmn) hx.2⟩

lemma isClosed_ballApprox (K : Set E) (hK : IsClosed K) (n : ℕ) :
    IsClosed (ballApprox K n) := hK.inter Metric.isClosed_closedBall

lemma isCompact_ballApprox [ProperSpace E] (K : Set E) (hK : IsClosed K) (n : ℕ) :
    IsCompact (ballApprox K n) :=
  (isCompact_closedBall (0 : E) (n : ℝ)).of_isClosed_subset
    (isClosed_ballApprox K hK n) inter_subset_right

lemma convex_ballApprox [NormedSpace ℝ E] (K : Set E) (hK : Convex ℝ K) (n : ℕ) :
    Convex ℝ (ballApprox K n) := hK.inter (convex_closedBall 0 (n : ℝ))

lemma zero_mem_ballApprox (K : Set E) (hK : (0 : E) ∈ K) (n : ℕ) :
    (0 : E) ∈ ballApprox K n := by
  refine ⟨hK, ?_⟩
  simp only [Metric.mem_closedBall, dist_self]
  exact Nat.cast_nonneg n

lemma eventually_mem_closedBall_nat (x : E) :
    ∀ᶠ n : ℕ in atTop, x ∈ Metric.closedBall (0 : E) (n : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop m] with n hn
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hm.trans (by exact_mod_cast hn)

/-- Every fixed point eventually sees exactly the original indicator value. -/
lemma indicator_ballApprox_eventually_eq (K : Set E) (x : E) :
    ∀ᶠ n : ℕ in atTop,
      (ballApprox K n).indicator (fun _ => (1 : ℝ)) x =
        K.indicator (fun _ => (1 : ℝ)) x := by
  classical
  filter_upwards [eventually_mem_closedBall_nat x] with n hn
  by_cases hx : x ∈ K <;> simp [ballApprox, hx, hn]

lemma indicator_ballApprox_tendsto (K : Set E) (x : E) :
    Tendsto (fun n : ℕ => (ballApprox K n).indicator (fun _ => (1 : ℝ)) x) atTop
      (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [indicator_ballApprox_eventually_eq K x] with n hn
  exact hn.symm

lemma iUnion_ballApprox (K : Set E) : (⋃ n, ballApprox K n) = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact hn.1
  · intro hx
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.mpr ⟨n, hx, by simpa only [Metric.mem_closedBall, dist_zero_right] using hn⟩

/-- Adding the same closed ball preserves the elementary exhaustion inclusion. -/
lemma ballApprox_add_closedBall_subset (K : Set E) (n : ℕ) (r : ℝ) :
    ballApprox K n + Metric.closedBall (0 : E) r ⊆ K + Metric.closedBall (0 : E) r := by
  rintro z ⟨x, hx, y, hy, hxy⟩
  exact ⟨x, hx.1, y, hy, hxy⟩

section Measure
variable [MeasurableSpace E] [BorelSpace E]

/-- The measure is the actual supplied probability measure; the convergence
uses dominated convergence of the real-valued indicators. -/
theorem measure_ballApprox_tendsto (μ : Measure E) [IsProbabilityMeasure μ]
    (K : Set E) (hK : IsClosed K) :
    Tendsto (fun n : ℕ => μ.real (ballApprox K n)) atTop (𝓝 (μ.real K)) := by
  classical
  have hm (n : ℕ) : MeasurableSet (ballApprox K n) := (isClosed_ballApprox K hK n).measurableSet
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ)
    (bound := fun _ : E => (1 : ℝ))
    (F := fun n : ℕ => (ballApprox K n).indicator (fun _ => (1 : ℝ)))
    (f := K.indicator (fun _ => (1 : ℝ)))
    (fun n => (measurable_const.indicator (hm n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n => ae_of_all _ (fun x => by by_cases hx : x ∈ ballApprox K n <;> simp [hx]))
    (ae_of_all _ (fun x => indicator_ballApprox_tendsto K x))
  have hi (n : ℕ) : (∫ x, (ballApprox K n).indicator (fun _ => (1 : ℝ)) x ∂μ) =
      μ.real (ballApprox K n) := integral_indicator_one (hm n)
  have hk : (∫ x, K.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real K :=
    integral_indicator_one hK.measurableSet
  simpa only [hi, hk] using hlim

/-- Interior endpoint probabilities remain interior for every sufficiently
large compact approximant. -/
theorem eventually_measure_ballApprox_mem_Ioo (μ : Measure E) [IsProbabilityMeasure μ]
    (K : Set E) (hK : IsClosed K) (hprob : μ.real K ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop, μ.real (ballApprox K n) ∈ Ioo (0 : ℝ) 1 :=
  (measure_ballApprox_tendsto μ K hK).eventually (isOpen_Ioo.mem_nhds hprob)

end Measure
end OAI.GaussianPropeller.ClosedBallApproximation
