import Tusnady.ConditionedGaussianConditional
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Gaussian tilting and Anderson's inequality

These lemmas prove the moment-control route via completing the square.
They use the already declared Anderson theorem, without adding literature
assumptions or weakening the claimed second-moment bound.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Tusnady

noncomputable def gaussianCoordinateShift {M : ℕ} (j : Fin M) (t : ℝ) : Fin M → ℝ :=
  fun i => if i = j then t else 0

theorem gaussianEnergy_sub_coordinateShift {M : ℕ} (j : Fin M) (t : ℝ) (z : Fin M → ℝ) :
    gaussianEnergy M (z - gaussianCoordinateShift j t) = gaussianEnergy M z - 2 * t * z j + t ^ 2 := by
  classical
  have hterm (i : Fin M) : (z i - gaussianCoordinateShift j t i) ^ 2 =
      (z i) ^ 2 + if i = j then (-2 * t * z j + t ^ 2) else 0 := by
    by_cases hi : i = j
    · subst i
      simp [gaussianCoordinateShift]
      ring
    · simp [gaussianCoordinateShift, hi]
  unfold gaussianEnergy
  simp_rw [Pi.sub_apply, hterm]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem standardGaussianDensity_complete_square {M : ℕ} (j : Fin M) (t : ℝ) (z : Fin M → ℝ) :
    standardGaussianDensity M z * Real.exp (t * z j) =
      Real.exp (t ^ 2 / 2) * standardGaussianDensity M (z - gaussianCoordinateShift j t) := by
  unfold standardGaussianDensity exponentialKernel
  rw [← Real.exp_add, ← Real.exp_add, gaussianEnergy_sub_coordinateShift]
  congr 1
  ring

theorem standardGaussian_centered (M : ℕ) :
    Literature.CenteredGaussian M (Literature.standardGaussian M) := by
  classical
  refine ⟨M, 1, ?_⟩
  have hfun : (fun z : Fin M → ℝ => fun i => ∑ j, (1 : Matrix (Fin M) (Fin M) ℝ) i j * z j) = id := by
    funext z i
    simp [Matrix.one_apply]
  rw [hfun, Measure.map_id]

theorem setIntegral_realDensityMeasure {X : Type*} [MeasurableSpace X]
    (base : Measure X) (f h : X → ℝ) (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x)
    {S : Set X} (hS : MeasurableSet S) :
    (∫ x in S, h x ∂realDensityMeasure base f) = ∫ x in S, f x * h x ∂base := by
  unfold realDensityMeasure
  rw [restrict_withDensity hS]
  exact integral_realDensityMeasure (base.restrict S) f h hfm hf

theorem setIntegral_standardGaussianDensity {M : ℕ} {K : Set (Fin M → ℝ)} (hK : MeasurableSet K) :
    (∫ z in K, standardGaussianDensity M z) = (Literature.standardGaussian M).real K := by
  have hnonneg : 0 ≤ ∫ z in K, standardGaussianDensity M z :=
    integral_nonneg (fun z => (Real.exp_pos _).le)
  rw [← standardGaussianDensity_measure_eq_literature, Measure.real_def,
    realDensityMeasure_apply volume (standardGaussianDensity M)
      (fun z => (Real.exp_pos _).le) (integrable_standardGaussianDensity M) hK,
    ENNReal.toReal_ofReal hnonneg]

theorem setIntegral_gaussianDensity_shift {M : ℕ} (K : Set (Fin M → ℝ)) (c : Fin M → ℝ) :
    (∫ z in K, standardGaussianDensity M (z - c)) =
      ∫ z in {z | z + c ∈ K}, standardGaussianDensity M z := by
  have h := (measurePreserving_add_right (volume : Measure (Fin M → ℝ)) c).setIntegral_preimage_emb
    (MeasurableEquiv.addRight c).measurableEmbedding (fun z => standardGaussianDensity M (z - c)) K
  simpa only [add_sub_cancel_right, Set.preimage, Function.comp_def] using h.symm

/-- Exact completion-square identity on an arbitrary measurable event. -/
theorem gaussian_restricted_exp_integral {M : ℕ} {K : Set (Fin M → ℝ)}
    (hK : MeasurableSet K) (j : Fin M) (t : ℝ) :
    (∫ z in K, Real.exp (t * z j) ∂Literature.standardGaussian M) =
      Real.exp (t ^ 2 / 2) * (Literature.standardGaussian M).real
        {z | z + gaussianCoordinateShift j t ∈ K} := by
  conv_lhs => rw [← standardGaussianDensity_measure_eq_literature,
    setIntegral_realDensityMeasure volume (standardGaussianDensity M) (fun z => Real.exp (t * z j))
      (continuous_exponentialKernel _ (continuous_gaussianEnergy M)).measurable
      (fun z => (Real.exp_pos _).le) hK]
  simp_rw [standardGaussianDensity_complete_square j t]
  have hShiftSet : MeasurableSet {z | z + gaussianCoordinateShift j t ∈ K} :=
    hK.preimage (by fun_prop)
  rw [integral_const_mul, setIntegral_gaussianDensity_shift,
    setIntegral_standardGaussianDensity hShiftSet]

theorem gaussian_restricted_exp_integral_le {M : ℕ} (anderson : Literature.Anderson)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hsymm : ∀ z : Fin M → ℝ, z ∈ K ↔ -z ∈ K) (j : Fin M) (t : ℝ) :
    (∫ z in K, Real.exp (t * z j) ∂Literature.standardGaussian M) ≤
      Real.exp (t ^ 2 / 2) * gaussianConditioningMass M K := by
  letI : IsProbabilityMeasure (Literature.standardGaussian M) := by
    unfold Literature.standardGaussian
    infer_instance
  have hshift := anderson M (Literature.standardGaussian M) (standardGaussian_centered M)
    K hK.isClosed hconvex hsymm (-gaussianCoordinateShift j t)
  simp only [sub_neg_eq_add] at hshift
  have hreal := ENNReal.toReal_mono (measure_ne_top (Literature.standardGaussian M) K) hshift
  have hp : (Literature.standardGaussian M).real K = gaussianConditioningMass M K := by
    rw [Measure.real_def, gaussianConditioningMass_eq_gaussian_measure M hK.measurableSet,
      ENNReal.toReal_ofReal (gaussianConditioningMass_nonneg M K)]
  rw [gaussian_restricted_exp_integral hK.measurableSet]
  exact mul_le_mul_of_nonneg_left (hreal.trans_eq hp) (Real.exp_pos _).le

/-- Every continuous scalar test has a finite conditional Gaussian
integral on a compact conditioning event. -/
theorem conditionedGaussian_test_integrable (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K)
    (test : (Fin M → ℝ) → ℝ) (htest : Continuous test) :
    Integrable test (ProbabilityTheory.cond (Literature.standardGaussian M) K) := by
  rw [← conditionedStandardGaussian_measure_eq_cond M hK.measurableSet hp]
  apply (integrable_realDensityMeasure_iff volume (conditionedStandardGaussianDensity M K) test
    (measurable_conditionedExponentialDensity volume hK.measurableSet _
      (continuous_gaussianEnergy M).measurable)
    (conditionedExponentialDensity_nonneg volume K _ _ hp)).mpr
  classical
  have hraw : IntegrableOn (fun z => standardGaussianDensity M z * test z) K :=
    (((continuous_exponentialKernel _ (continuous_gaussianEnergy M)).mul htest).continuousOn.integrableOn_compact hK)
  have heq : (fun z => conditionedStandardGaussianDensity M K z * test z) =
      K.indicator (fun z => standardGaussianDensity M z * test z / gaussianConditioningMass M K) := by
    funext z
    by_cases hz : z ∈ K
    · simp only [conditionedStandardGaussianDensity, conditionedExponentialDensity, indicator_of_mem hz,
        standardGaussianDensity, gaussianConditioningMass]
      ring
    · simp [conditionedStandardGaussianDensity, conditionedExponentialDensity, hz]
  rw [heq]
  exact (integrable_indicator_iff hK.measurableSet).mpr (hraw.div_const _)

/-- Anderson implies that each actual conditioned coordinate is
sub-Gaussian with unit variance proxy. -/
theorem conditionedGaussian_exp_integral_le {M : ℕ} (anderson : Literature.Anderson)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (hconvex : Convex ℝ K)
    (hsymm : ∀ z : Fin M → ℝ, z ∈ K ↔ -z ∈ K)
    (hp : 0 < gaussianConditioningMass M K) (j : Fin M) (t : ℝ) :
    (∫ z, Real.exp (t * z j) ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) ≤
      Real.exp (t ^ 2 / 2) := by
  rw [ProbabilityTheory.cond, integral_smul_measure,
    gaussianConditioningMass_eq_gaussian_measure M hK.measurableSet,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left
    (gaussian_restricted_exp_integral_le anderson hK hconvex hsymm j t) (inv_nonneg.mpr hp.le)
  have heq : (gaussianConditioningMass M K)⁻¹ *
      (Real.exp (t ^ 2 / 2) * gaussianConditioningMass M K) = Real.exp (t ^ 2 / 2) := by
    field_simp
  exact h.trans_eq heq

end Tusnady
