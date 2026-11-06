import Tusnady.Upper.Ehrhard.HeatTransport
import Tusnady.Upper.Ehrhard.PolyhedralApproximation

/-!
# Gaussian quantile concavity for polyhedral sections

The proof combines the smooth analytic theorem, linear-kernel approximation
and the boundary-preserving soft minimum.  No Ehrhard or Gaussian-isoperimetry
statement is assumed.  The displayed kernel approximation is mathematical
data, to be supplied by the proved coordinate-projection construction.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace BigOperators NNReal
namespace OAI.GaussianPropeller.EhrhardSmooth
open Quantile AffineSoftMin
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι

/-- Gaussian probability of an affine section of a finite closed halfspace intersection. -/
def polyhedralProbability (v : κ → E) (b : κ → ℝ) (A : E →L[ℝ] E) (x : E) : ℝ :=
  (gaussianMeasure ι).real ((fun z => x + A z) ⁻¹' slackSet v b)

theorem approx_quantileLinearHeat_concave
    (v : κ → E) (b : κ → ℝ) (A : E →L[ℝ] E)
    (e : ℕ → E ≃L[ℝ] E) (he : ∀ z, Tendsto (fun n => e n z) atTop (𝓝 (A z)))
    (n : ℕ) : ConcaveOn ℝ univ (quantileLinearHeat (approxValue n v b) A) := by
  classical
  let L : ℝ≥0 := ∑ i, ‖v i‖₊
  have hL (i : κ) : ‖v i‖ ≤ (L : ℝ) := by
    exact_mod_cast (Finset.single_le_sum (f := fun j => ‖v j‖₊)
      (fun j _ => bot_le) (Finset.mem_univ i))
  let Ln : ℝ≥0 := ⟨(n : ℝ)^2 * (L : ℝ), by positivity⟩
  exact quantileLinearHeat_concave_of_equiv_approx
    (approxValue_fderiv n v b) (approxGrad_fderiv n v b) (approxHess_continuous n v b)
    (L := Ln) (approxGrad_bound n v b hL) (approxHess_bound n v b L.coe_nonneg hL)
    (approxValue_concave n v b) A e he

theorem approx_quantileLinearHeat_limit
    (v : κ → E) (b : κ → ℝ) (A : E →L[ℝ] E) (x : E)
    (hp : polyhedralProbability v b A x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun n => quantileLinearHeat (approxValue n v b) A x) atTop
      (𝓝 (q (polyhedralProbability v b A x))) := by
  exact (continuousAt_q hp).tendsto.comp
    (integral_cdf_approxValue_limit (gaussianMeasure ι) v b (fun z => x + A z) (by fun_prop))

/-- The CDF form also covers a zero or full probability at the interpolated
point; only the two endpoint quantiles need to be finite. -/
theorem polyhedralProbability_cdf_concavity
    (v : κ → E) (b : κ → ℝ) (A : E →L[ℝ] E)
    (e : ℕ → E ≃L[ℝ] E) (he : ∀ z, Tendsto (fun n => e n z) atTop (𝓝 (A z)))
    (x y : E) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hx : polyhedralProbability v b A x ∈ Ioo (0 : ℝ) 1)
    (hy : polyhedralProbability v b A y ∈ Ioo (0 : ℝ) 1) :
    Φ (a * q (polyhedralProbability v b A x) + c * q (polyhedralProbability v b A y)) ≤
      polyhedralProbability v b A (a • x + c • y) := by
  have hleft := continuous_Φ.continuousAt.tendsto.comp
    (((approx_quantileLinearHeat_limit v b A x hx).const_mul a).add
      ((approx_quantileLinearHeat_limit v b A y hy).const_mul c))
  have hright := integral_cdf_approxValue_limit (gaussianMeasure ι) v b
    (fun z => (a • x + c • y) + A z) (by fun_prop)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  have hconc := (approx_quantileLinearHeat_concave v b A e he n).2
    (mem_univ x) (mem_univ y) ha hc hac
  have h := strictMono_Φ.monotone hconc
  have hcf : Continuous (approxValue n v b) :=
    continuous_iff_continuousAt.mpr (fun z => (approxValue_fderiv n v b z).continuousAt)
  have hmem : (∫ z, Φ (approxValue n v b ((a • x + c • y) + A z)) ∂gaussianMeasure ι) ∈
      Ioo (0 : ℝ) 1 := integral_Φ_mem
    (hcf.comp (show Continuous (fun z => (a • x + c • y) + A z) by fun_prop)).aestronglyMeasurable
  simpa only [Function.comp_def, quantileLinearHeat, smul_eq_mul, Φ_q hmem] using h

/-- Finite-quantile form, with all three probabilities explicitly in (0,1). -/
theorem polyhedralProbability_quantile_concavity
    (v : κ → E) (b : κ → ℝ) (A : E →L[ℝ] E)
    (e : ℕ → E ≃L[ℝ] E) (he : ∀ z, Tendsto (fun n => e n z) atTop (𝓝 (A z)))
    (x y : E) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hx : polyhedralProbability v b A x ∈ Ioo (0 : ℝ) 1)
    (hy : polyhedralProbability v b A y ∈ Ioo (0 : ℝ) 1)
    (hz : polyhedralProbability v b A (a • x + c • y) ∈ Ioo (0 : ℝ) 1) :
    a * q (polyhedralProbability v b A x) + c * q (polyhedralProbability v b A y) ≤
      q (polyhedralProbability v b A (a • x + c • y)) := by
  apply strictMono_Φ.le_iff_le.mp
  rw [Φ_q hz]
  exact polyhedralProbability_cdf_concavity v b A e he x y ha hc hac hx hy

end OAI.GaussianPropeller.EhrhardSmooth
