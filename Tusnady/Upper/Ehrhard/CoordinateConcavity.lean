import Tusnady.Upper.Ehrhard.PolyhedralConcavity
import Tusnady.Upper.Ehrhard.ProjectionApproximation

/-!
# Quantile concavity under actual partial Gaussian smoothing

The noise kernel is now the concrete coordinate projection, and all its
approximation data are supplied by proved invertible diagonal maps.
There is no kernel-existence or Gaussian-concavity assumption in these results.
-/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace NNReal
namespace OAI.GaussianPropeller.EhrhardSmooth
open Quantile
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι

theorem quantileLinearHeat_concave_projection
    {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hK : Continuous K)
    {L : ℝ≥0} {D : ℝ} (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D)
    (hconc : ConcaveOn ℝ univ f) (keep : ι → Bool) :
    ConcaveOn ℝ univ (quantileLinearHeat f (CoordinateProjection.projection keep)) :=
  quantileLinearHeat_concave_of_equiv_approx hf hg hK hL hD hconc _
    (CoordinateProjection.approximant keep) (CoordinateProjection.approximant_limit keep)

/-- An unconditional Gaussian section inequality for finite closed halfspace
intersections.  Discarded coordinates are deterministic section parameters;
retained coordinates carry the actual standard Gaussian noise. -/
theorem polyhedralProbability_projection_cdf_concavity
    (v : κ → E) (b : κ → ℝ) (keep : ι → Bool)
    (x y : E) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hx : polyhedralProbability v b (CoordinateProjection.projection keep) x ∈ Ioo (0 : ℝ) 1)
    (hy : polyhedralProbability v b (CoordinateProjection.projection keep) y ∈ Ioo (0 : ℝ) 1) :
    Φ (a * q (polyhedralProbability v b (CoordinateProjection.projection keep) x) +
      c * q (polyhedralProbability v b (CoordinateProjection.projection keep) y)) ≤
      polyhedralProbability v b (CoordinateProjection.projection keep) (a • x + c • y) :=
  polyhedralProbability_cdf_concavity v b _ (CoordinateProjection.approximant keep)
    (CoordinateProjection.approximant_limit keep) x y ha hc hac hx hy

theorem polyhedralProbability_projection_quantile_concavity
    (v : κ → E) (b : κ → ℝ) (keep : ι → Bool)
    (x y : E) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hx : polyhedralProbability v b (CoordinateProjection.projection keep) x ∈ Ioo (0 : ℝ) 1)
    (hy : polyhedralProbability v b (CoordinateProjection.projection keep) y ∈ Ioo (0 : ℝ) 1)
    (hz : polyhedralProbability v b (CoordinateProjection.projection keep) (a • x + c • y) ∈
      Ioo (0 : ℝ) 1) :
    a * q (polyhedralProbability v b (CoordinateProjection.projection keep) x) +
      c * q (polyhedralProbability v b (CoordinateProjection.projection keep) y) ≤
      q (polyhedralProbability v b (CoordinateProjection.projection keep) (a • x + c • y)) :=
  polyhedralProbability_quantile_concavity v b _ (CoordinateProjection.approximant keep)
    (CoordinateProjection.approximant_limit keep) x y ha hc hac hx hy hz

end OAI.GaussianPropeller.EhrhardSmooth
