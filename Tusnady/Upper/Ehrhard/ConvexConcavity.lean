import Tusnady.Upper.Ehrhard.CoordinateConcavity
import Tusnady.Upper.Ehrhard.ConvexApproximation

/-!
# Gaussian quantile inequality for general closed convex sections

Countably many supporting halfspaces, finite outer intersections and dominated
convergence extend the proved polyhedral inequality to every closed convex set.
No full dimension, boundary-null or positive-density condition is needed.
The endpoint quantiles are explicitly restricted to probabilities in (0,1).
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace OAI.GaussianPropeller.EhrhardSmooth
open Quantile ConvexApproximation
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def sectionProbability (K : Set E) (A : E →L[ℝ] E) (x : E) : ℝ :=
  (gaussianMeasure ι).real ((fun z => x + A z) ⁻¹' K)

/-- The Gaussian CDF formulation remains meaningful even if the interpolated
section has zero or full mass.  All analytic and approximation steps are proved. -/
theorem closedConvexProbability_cdf_concavity
    (K : Set E) (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (A : E →L[ℝ] E)
    (e : ℕ → E ≃L[ℝ] E) (he : ∀ z, Tendsto (fun n => e n z) atTop (𝓝 (A z)))
    (x y : E) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hx : sectionProbability K A x ∈ Ioo (0 : ℝ) 1)
    (hy : sectionProbability K A y ∈ Ioo (0 : ℝ) 1) :
    Φ (a * q (sectionProbability K A x) + c * q (sectionProbability K A y)) ≤
      sectionProbability K A (a • x + c • y) := by
  obtain ⟨v, b, hrep⟩ := exists_countable_slack_representation K hKclosed hKconvex
  let p : ℕ → E → ℝ := fun n z => polyhedralProbability
    (fun i : Fin (n+1) => v i.val) (fun i => b i.val) A z
  have hp (z : E) : Tendsto (fun n => p n z) atTop (𝓝 (sectionProbability K A z)) := by
    exact measure_outerSet_tendsto (gaussianMeasure ι) K hKclosed v b hrep
      (fun w => z + A w) (by fun_prop)
  have hqx := (continuousAt_q hx).tendsto.comp (hp x)
  have hqy := (continuousAt_q hy).tendsto.comp (hp y)
  have hleft := continuous_Φ.continuousAt.tendsto.comp
    ((hqx.const_mul a).add (hqy.const_mul c))
  apply le_of_tendsto_of_tendsto hleft (hp (a • x + c • y))
  have hxe : ∀ᶠ n in atTop, p n x ∈ Ioo (0 : ℝ) 1 := (hp x).eventually (isOpen_Ioo.mem_nhds hx)
  have hye : ∀ᶠ n in atTop, p n y ∈ Ioo (0 : ℝ) 1 := (hp y).eventually (isOpen_Ioo.mem_nhds hy)
  filter_upwards [hxe, hye] with n hnx hny
  exact polyhedralProbability_cdf_concavity
    (fun i : Fin (n+1) => v i.val) (fun i => b i.val) A e he x y ha hc hac hnx hny

/-- Actual partial Gaussian smoothing of a general closed convex set.
There is no unproved analytic input or assumed kernel approximation. -/
theorem closedConvexProbability_projection_cdf_concavity
    (K : Set E) (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (keep : ι → Bool)
    (x y : E) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hx : sectionProbability K (CoordinateProjection.projection keep) x ∈ Ioo (0 : ℝ) 1)
    (hy : sectionProbability K (CoordinateProjection.projection keep) y ∈ Ioo (0 : ℝ) 1) :
    Φ (a * q (sectionProbability K (CoordinateProjection.projection keep) x) +
      c * q (sectionProbability K (CoordinateProjection.projection keep) y)) ≤
      sectionProbability K (CoordinateProjection.projection keep) (a • x + c • y) :=
  closedConvexProbability_cdf_concavity K hKclosed hKconvex _
    (CoordinateProjection.approximant keep) (CoordinateProjection.approximant_limit keep)
    x y ha hc hac hx hy

theorem closedConvexProbability_projection_quantile_concavity
    (K : Set E) (hKclosed : IsClosed K) (hKconvex : Convex ℝ K) (keep : ι → Bool)
    (x y : E) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hx : sectionProbability K (CoordinateProjection.projection keep) x ∈ Ioo (0 : ℝ) 1)
    (hy : sectionProbability K (CoordinateProjection.projection keep) y ∈ Ioo (0 : ℝ) 1)
    (hz : sectionProbability K (CoordinateProjection.projection keep) (a • x + c • y) ∈
      Ioo (0 : ℝ) 1) :
    a * q (sectionProbability K (CoordinateProjection.projection keep) x) +
      c * q (sectionProbability K (CoordinateProjection.projection keep) y) ≤
      q (sectionProbability K (CoordinateProjection.projection keep) (a • x + c • y)) := by
  apply strictMono_Φ.le_iff_le.mp
  rw [Φ_q hz]
  exact closedConvexProbability_projection_cdf_concavity K hKclosed hKconvex keep x y ha hc hac hx hy

end OAI.GaussianPropeller.EhrhardSmooth
