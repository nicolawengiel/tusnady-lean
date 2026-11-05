import Tusnady.ConditionedGaussianDensity
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Tusnady.Literature

/-! # Concrete finite-dimensional standard Gaussian densities and entropy -/

open MeasureTheory Set Real
open scoped BigOperators

namespace Tusnady

noncomputable def gaussianEnergy (M : ℕ) (z : Fin M → ℝ) : ℝ := ∑ i, (z i) ^ 2

noncomputable def gaussianEntropyConstant (M : ℕ) : ℝ :=
  (M : ℝ) / 2 * Real.log (2 * Real.pi)

noncomputable def standardGaussianDensity (M : ℕ) : (Fin M → ℝ) → ℝ :=
  exponentialKernel (gaussianEntropyConstant M) (gaussianEnergy M)

theorem gaussianEnergy_nonneg (M : ℕ) (z : Fin M → ℝ) : 0 ≤ gaussianEnergy M z := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (z i)

theorem continuous_gaussianEnergy (M : ℕ) : Continuous (gaussianEnergy M) := by
  unfold gaussianEnergy
  fun_prop

theorem standardGaussianDensity_eq_prod (M : ℕ) (z : Fin M → ℝ) :
    standardGaussianDensity M z =
      ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (z i) := by
  have hpos : 0 < 2 * Real.pi := by positivity
  have hfactor (x : ℝ) : Real.exp (-Real.log (2 * Real.pi) / 2 - x ^ 2 / 2) =
      ProbabilityTheory.gaussianPDFReal 0 1 x := by
    unfold ProbabilityTheory.gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero]
    calc
      _ = Real.exp (-Real.log (Real.sqrt (2 * Real.pi))) * Real.exp (-x ^ 2 / 2) := by
        rw [← Real.exp_add, Real.log_sqrt hpos.le]
        congr 1
        ring
      _ = _ := by rw [Real.exp_neg, Real.exp_log (Real.sqrt_pos.mpr hpos)]
  unfold standardGaussianDensity exponentialKernel gaussianEntropyConstant gaussianEnergy
  calc
    _ = Real.exp (∑ i : Fin M, (-Real.log (2 * Real.pi) / 2 - (z i) ^ 2 / 2)) := by
      congr 1
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.sum_div]
      ring
    _ = ∏ i : Fin M, Real.exp (-Real.log (2 * Real.pi) / 2 - (z i) ^ 2 / 2) :=
      Real.exp_sum _ _
    _ = _ := Finset.prod_congr rfl fun i _ => hfactor (z i)

/-- The explicitly defined multivariate density is normalized, proved by
the finite Fubini product formula and mathlib's one-dimensional Gaussian
normalization. -/
theorem integral_standardGaussianDensity (M : ℕ) :
    (∫ z, standardGaussianDensity M z) = 1 := by
  simp_rw [standardGaussianDensity_eq_prod]
  rw [integral_fintype_prod_volume_eq_prod]
  simp [ProbabilityTheory.integral_gaussianPDFReal_eq_one]

theorem integrable_standardGaussianDensity (M : ℕ) :
    Integrable (standardGaussianDensity M) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_standardGaussianDensity]
  exact one_ne_zero

/-- The density representation agrees with the independent-coordinate
Gaussian measure used by the explicitly documented literature interface. -/
theorem standardGaussianDensity_measure_eq_pi (M : ℕ) :
    realDensityMeasure volume (standardGaussianDensity M) =
      Measure.pi (fun _ : Fin M => ProbabilityTheory.gaussianReal 0 1) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  change (realDensityMeasure volume
    (exponentialKernel (gaussianEntropyConstant M) (gaussianEnergy M))) (Set.univ.pi s) = _
  rw [exponentialEventMass_eq_measure volume (MeasurableSet.univ_pi hs)
    (gaussianEntropyConstant M) (gaussianEnergy M)
    (integrable_standardGaussianDensity M).integrableOn]
  change ENNReal.ofReal (∫ z in Set.univ.pi s, standardGaussianDensity M z) = _
  simp_rw [ProbabilityTheory.gaussianReal_apply_eq_integral 0 (v := 1) (by norm_num)]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 1 x)]
  congr 1
  simp_rw [standardGaussianDensity_eq_prod]
  change (∫ z, ∏ i, ProbabilityTheory.gaussianPDFReal 0 1 (z i)
    ∂(Measure.pi (fun _ : Fin M => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]

theorem standardGaussianDensity_measure_eq_literature (M : ℕ) :
    realDensityMeasure volume (standardGaussianDensity M) =
      Literature.standardGaussian M := standardGaussianDensity_measure_eq_pi M

noncomputable def gaussianConditioningMass (M : ℕ) (K : Set (Fin M → ℝ)) : ℝ :=
  exponentialEventMass volume K (gaussianEntropyConstant M) (gaussianEnergy M)

noncomputable def conditionedStandardGaussianDensity (M : ℕ)
    (K : Set (Fin M → ℝ)) : (Fin M → ℝ) → ℝ :=
  conditionedExponentialDensity volume K (gaussianEntropyConstant M) (gaussianEnergy M)

theorem gaussianConditioningMass_nonneg (M : ℕ) (K : Set (Fin M → ℝ)) :
    0 ≤ gaussianConditioningMass M K :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- The conditioning probability in the entropy formula is the actual
Gaussian event probability from the literature interface. -/
theorem gaussianConditioningMass_eq_gaussian_measure (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : MeasurableSet K) :
    Literature.standardGaussian M K = ENNReal.ofReal (gaussianConditioningMass M K) := by
  rw [← standardGaussianDensity_measure_eq_literature]
  exact exponentialEventMass_eq_measure volume hK _ _
    (integrable_standardGaussianDensity M).integrableOn

/-- The conditioned density is exactly the conditional Gaussian law
appearing in the manuscript, with no identification hypothesis. -/
theorem conditionedStandardGaussian_measure_eq_cond (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : MeasurableSet K) (hp : 0 < gaussianConditioningMass M K) :
    realDensityMeasure volume (conditionedStandardGaussianDensity M K) =
      ProbabilityTheory.cond (Literature.standardGaussian M) K := by
  rw [← standardGaussianDensity_measure_eq_literature]
  exact conditionedExponentialDensity_measure_eq_cond volume hK _
    (continuous_gaussianEnergy M).measurable hp
    (integrable_standardGaussianDensity M).integrableOn

theorem conditionedStandardGaussian_energy_moment (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : MeasurableSet K) (hp : 0 < gaussianConditioningMass M K) :
    (∫ z, gaussianEnergy M z ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) =
      ∫ z, conditionedStandardGaussianDensity M K z * gaussianEnergy M z := by
  rw [← conditionedStandardGaussian_measure_eq_cond M hK hp]
  exact integral_realDensityMeasure volume (conditionedStandardGaussianDensity M K)
    (gaussianEnergy M)
    (measurable_conditionedExponentialDensity volume hK _ (continuous_gaussianEnergy M).measurable)
    (conditionedExponentialDensity_nonneg volume K _ _ hp)

/-- Formula (6.3) for the concrete density on a compact conditioning
event. All moments are actual Lebesgue integrals. -/
theorem conditionedStandardGaussian_entropy_eq (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K) :
    densityEntropy volume (conditionedStandardGaussianDensity M K) =
      (M : ℝ) / 2 * Real.log (2 * Real.pi) +
      (1 / 2 : ℝ) * (∫ z, conditionedStandardGaussianDensity M K z * gaussianEnergy M z) +
      Real.log (gaussianConditioningMass M K) := by
  exact conditionedExponentialDensity_entropy_eq_of_isCompact volume hK
    (gaussianEntropyConstant M) (continuous_gaussianEnergy M) hp

theorem conditionedStandardGaussian_entropy_lower (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K) :
    (M : ℝ) / 2 * Real.log (2 * Real.pi) + Real.log (gaussianConditioningMass M K) ≤
      densityEntropy volume (conditionedStandardGaussianDensity M K) := by
  exact conditionedExponentialDensity_entropy_lower volume hK.measurableSet
    (gaussianEntropyConstant M) (gaussianEnergy M) hp
    ((continuous_exponentialKernel _ (continuous_gaussianEnergy M)).continuousOn.integrableOn_compact hK)
    (integrable_conditionedEnergy_of_isCompact volume hK _ (continuous_gaussianEnergy M))
    (gaussianEnergy_nonneg M)

/-- Formula (6.3), now with its energy moment written under the actual
conditioned Gaussian probability law. -/
theorem conditionedStandardGaussian_entropy_eq_cond_moment (M : ℕ)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K)
    (hp : 0 < gaussianConditioningMass M K) :
    densityEntropy volume (conditionedStandardGaussianDensity M K) =
      (M : ℝ) / 2 * Real.log (2 * Real.pi) + (1 / 2 : ℝ) *
        (∫ z, gaussianEnergy M z ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) +
      Real.log (gaussianConditioningMass M K) := by
  rw [conditionedStandardGaussian_energy_moment M hK.measurableSet hp]
  exact conditionedStandardGaussian_entropy_eq M hK hp

/-- The concrete entropy lower bound when the Gaussian small-ball
probability is at least `exp(-kappa*M)`. -/
theorem conditionedStandardGaussian_entropy_lower_of_probability (M : ℕ)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (kappa : ℝ)
    (hmass : ENNReal.ofReal (Real.exp (-kappa * M)) ≤ Literature.standardGaussian M K) :
    (M : ℝ) / 2 * Real.log (2 * Real.pi) - kappa * M ≤
      densityEntropy volume (conditionedStandardGaussianDensity M K) := by
  rw [gaussianConditioningMass_eq_gaussian_measure M hK.measurableSet] at hmass
  have hpExp : Real.exp (-kappa * M) ≤ gaussianConditioningMass M K :=
    (ENNReal.ofReal_le_ofReal_iff (gaussianConditioningMass_nonneg M K)).mp hmass
  have hp : 0 < gaussianConditioningMass M K := lt_of_lt_of_le (Real.exp_pos _) hpExp
  have hlog : -kappa * M ≤ Real.log (gaussianConditioningMass M K) :=
    (Real.le_log_iff_exp_le hp).mpr hpExp
  have h := conditionedStandardGaussian_entropy_lower M hK hp
  linarith

end Tusnady
