import Tusnady.ConditionedGaussianSecondMoment
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual entropy-to-discrepancy obstruction

The quantitative correlations, product-uniform coefficient law, and
conditioned second moment are proved/imported from their concrete results.
Only actual response, pointwise duality and error data of the geometric
construction remain inputs. No positive-correlation hypothesis is added.
-/

open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace Tusnady

theorem integrable_inner_of_memLp_two {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure Ω}
    (Z err : Ω → E) (hZ : MemLp Z 2 μ) (he : MemLp err 2 μ) :
    Integrable (fun ω => inner ℝ (Z ω) (err ω)) μ := by
  have hi := L2.integrable_inner (𝕜 := ℝ) (hZ.toLp Z) (he.toLp err)
  apply hi.congr
  filter_upwards [hZ.coeFn_toLp, he.coeFn_toLp] with ω hZω heω
  rw [hZω, heω]

theorem integral_error_lower_bound_of_memLp {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure Ω}
    (Z err : Ω → E) (hZ : MemLp Z 2 μ) (he : MemLp err 2 μ)
    {mass q : ℝ} (hmass : 0 ≤ mass) (hq : 0 ≤ q)
    (hz : (∫ ω, ‖Z ω‖ ^ 2 ∂μ) ≤ mass)
    (herr : (∫ ω, ‖err ω‖ ^ 2 ∂μ) ≤ q ^ 2 * mass) :
    -(q * mass) ≤ ∫ ω, inner ℝ (Z ω) (err ω) ∂μ := by
  have hzEq : (∫ ω, ‖(hZ.toLp Z) ω‖ ^ 2 ∂μ) = ∫ ω, ‖Z ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZ.coeFn_toLp] with ω hω
    rw [hω]
  have heEq : (∫ ω, ‖(he.toLp err) ω‖ ^ 2 ∂μ) = ∫ ω, ‖err ω‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [he.coeFn_toLp] with ω hω
    rw [hω]
  have hiEq : (∫ ω, inner ℝ ((hZ.toLp Z) ω) ((he.toLp err) ω) ∂μ) =
      ∫ ω, inner ℝ (Z ω) (err ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hZ.coeFn_toLp, he.coeFn_toLp] with ω hZω heω
    rw [hZω, heω]
  have h := integral_error_lower_bound (hZ.toLp Z) (he.toLp err) hmass hq
    (hzEq.trans_le hz) (heEq.trans_le herr)
  rwa [hiEq] at h

theorem euclideanVector_norm_sq {M : ℕ} (z : Fin M → ℝ) :
    ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin M))‖ ^ 2 = gaussianEnergy M z := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  rfl

theorem euclideanVector_inner_diagonal {M : ℕ} (z u weight : Fin M → ℝ) :
    inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin M))
      (WithLp.toLp 2 (fun j => weight j * u j)) = ∑ j, weight j * (z j * u j) := by
  rw [EuclideanSpace.inner_toLp_toLp]
  apply Finset.sum_congr rfl
  intro j _
  change (weight j * u j) * z j = weight j * (z j * u j)
  ring

/-- Main.pdf Proposition 6.3, with the Gaussian law, Rosenblatt transform,
correlations and second moment actually derived. The response assumptions
are pointwise construction data; the error bound uses the actual uniform
coefficient distribution. -/
theorem conditionedGaussian_obstruction (literature : Literature.Assumptions)
    (M : ℕ) (hM : 0 < M) {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hsymm : ∀ z : Fin M → ℝ, z ∈ K ↔ -z ∈ K)
    (hp : 0 < gaussianConditioningMass M K) (kappa : ℝ)
    (hmass : ENNReal.ofReal (Real.exp (-kappa * M)) ≤ Literature.standardGaussian M K)
    (weight : Fin M → ℝ) (smin rho t : ℝ) (hsmin : 0 ≤ smin) (hrho : 0 ≤ rho)
    (hweight : ∀ j, smin ≤ weight j)
    (V err : (Fin M → ℝ) → EuclideanSpace ℝ (Fin M)) (herrcont : Continuous err)
    (hresponse : ∀ u ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      V u = WithLp.toLp 2 (fun j => weight j * u j) + err u)
    (hdual : ∀ z ∈ K, ∀ u ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin M)) (V u) ≤ t)
    (herr : (∫ u, ‖err u‖ ^ 2 ∂Measure.pi (fun _ : Fin M =>
      ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1 : ℝ) 1))) ≤
      (rho * smin) ^ 2 * M) :
    (gaussianRosenblattConstant kappa - rho) * smin * M ≤ t := by
  let s := conditionedGaussianConditionalSystem M hK hp
  let ν := ProbabilityTheory.cond (Literature.standardGaussian M) K
  let U := s.cdfTransform
  let Z : (Fin M → ℝ) → EuclideanSpace ℝ (Fin M) := fun z => WithLp.toLp 2 z
  have hlaw : s.law = ν := conditionedGaussianConditionalSystem_law M hK hp
  letI : IsProbabilityMeasure ν := by rw [← hlaw]; infer_instance
  obtain ⟨hUm, hUniform, hCorrNonneg, hCorr⟩ :=
    conditionedGaussian_rosenblatt_facts literature M hM hK hp kappa hmass
  have hUcube (z : Fin M → ℝ) : U z ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
    exact ⟨fun j => (abs_le.mp (s.cdfTransform_abs_le_one z j)).1,
      fun j => (abs_le.mp (s.cdfTransform_abs_le_one z j)).2⟩
  have hZcont : Continuous Z := PiLp.continuous_toLp 2 (fun _ : Fin M => ℝ)
  have hZLp : MemLp Z 2 ν := by
    apply (memLp_two_iff_integrable_sq_norm hZcont.measurable.aestronglyMeasurable).mpr
    exact conditionedGaussian_test_integrable M hK hp (fun z => ‖Z z‖ ^ 2) (by fun_prop)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image herrcont).isBounded.exists_norm_le
  have hErrLp : MemLp (fun z => err (U z)) 2 ν := by
    apply MemLp.of_bound (herrcont.measurable.comp hUm).aestronglyMeasurable B
    exact Filter.Eventually.of_forall fun z => hB _ ⟨U z, hUcube z, rfl⟩
  have hz : (∫ z, ‖Z z‖ ^ 2 ∂ν) ≤ (M : ℝ) := by
    simp_rw [show ∀ z, ‖Z z‖ ^ 2 = gaussianEnergy M z from euclideanVector_norm_sq]
    exact conditionedGaussian_secondMoment M literature.anderson hK hconvex hsymm hp
  have herrMoment : (∫ z, ‖err (U z)‖ ^ 2 ∂ν) ≤ (rho * smin) ^ 2 * M := by
    have heq := integral_map (μ := ν) hUm.aemeasurable
      (herrcont.norm.pow 2).measurable.aestronglyMeasurable
    simp only [Pi.pow_apply, Function.comp_def] at heq
    rw [hUniform] at heq
    rw [← heq]
    exact herr
  have hErrLower := integral_error_lower_bound_of_memLp Z (fun z => err (U z)) hZLp hErrLp
    (Nat.cast_nonneg M) (mul_nonneg hrho hsmin) hz herrMoment
  have hErrInt := integrable_inner_of_memLp_two Z (fun z => err (U z)) hZLp hErrLp
  have hCorrInt (j : Fin M) : Integrable (fun z => z j * U z j) ν := by
    rw [← hlaw]
    exact s.coordinate_correlation_integrable j
  have hSumInt : Integrable (fun z => ∑ j, weight j * (z j * U z j)) ν :=
    integrable_finset_sum Finset.univ (fun j _ => (hCorrInt j).const_mul (weight j))
  have hPoint : ∀ᵐ z ∂ν, (∑ j, weight j * (z j * U z j)) + inner ℝ (Z z) (err (U z)) ≤ t := by
    filter_upwards [ProbabilityTheory.ae_cond_mem hK.measurableSet] with z hzK
    have hd := hdual z hzK (U z) (hUcube z)
    rw [hresponse (U z) (hUcube z), inner_add_right, euclideanVector_inner_diagonal] at hd
    exact hd
  have hUpper := integral_mono_ae (hSumInt.add hErrInt) (integrable_const t) hPoint
  simp only [Pi.add_apply] at hUpper
  rw [integral_add (f := fun z => ∑ j, weight j * (z j * U z j))
    (g := fun z => inner ℝ (Z z) (err (U z))) hSumInt hErrInt,
    integral_finset_sum Finset.univ (fun j _ => (hCorrInt j).const_mul (weight j))] at hUpper
  simp_rw [integral_const_mul] at hUpper
  simp only [integral_const, probReal_univ, one_smul] at hUpper
  apply small_ball_obstruction_core weight (fun j => ∫ z, z j * U z j ∂ν)
    hsmin hCorrNonneg hweight hCorr
  · simpa only [mul_assoc] using hErrLower
  · exact hUpper

end Tusnady
