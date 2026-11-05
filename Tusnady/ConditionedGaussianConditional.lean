import Tusnady.ConditionedGaussianFinite
import Tusnady.EntropyDensitySystemConstruction
import Tusnady.EntropyDensityConditionalIntegrability

/-! # The actual conditional-density system of the conditioned Gaussian -/

open MeasureTheory Set

namespace Tusnady

noncomputable def compactDensityRadius {M : ℕ} (K : Set (Fin M → ℝ)) (hK : IsCompact K) : ℝ :=
  max (Classical.choose hK.isBounded.exists_norm_le) 0

theorem compactDensityRadius_nonneg {M : ℕ} (K : Set (Fin M → ℝ)) (hK : IsCompact K) :
    0 ≤ compactDensityRadius K hK := le_max_right _ _

theorem compactDensityRadius_bounds {M : ℕ} (K : Set (Fin M → ℝ)) (hK : IsCompact K)
    (z : Fin M → ℝ) (hz : z ∈ K) (j : Fin M) : |z j| ≤ compactDensityRadius K hK := by
  have hnorm := Classical.choose_spec hK.isBounded.exists_norm_le z hz
  have hj : |z j| ≤ ‖z‖ := norm_le_pi_norm z j
  exact hj.trans (hnorm.trans (le_max_left _ _))

theorem conditionedStandardGaussianDensity_bound (M : ℕ) (K : Set (Fin M → ℝ))
    (hp : 0 < gaussianConditioningMass M K) (z : Fin M → ℝ) :
    conditionedStandardGaussianDensity M K z ≤
      Real.exp (-gaussianEntropyConstant M) / gaussianConditioningMass M K := by
  classical
  by_cases hz : z ∈ K
  · change K.indicator (fun z => exponentialKernel (gaussianEntropyConstant M) (gaussianEnergy M) z /
      gaussianConditioningMass M K) z ≤ _
    rw [indicator_of_mem hz]
    apply div_le_div_of_nonneg_right _ hp.le
    unfold exponentialKernel
    apply Real.exp_le_exp.mpr
    have he := gaussianEnergy_nonneg M z
    linarith
  · change K.indicator (fun z => exponentialKernel (gaussianEntropyConstant M) (gaussianEnergy M) z /
      gaussianConditioningMass M K) z ≤ _
    rw [indicator_of_notMem hz]
    positivity

theorem conditionedStandardGaussianDensity_support (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (z : Fin M → ℝ) (j : Fin M)
    (hz : compactDensityRadius K hK < |z j|) :
    conditionedStandardGaussianDensity M K z = 0 := by
  classical
  have hzK : z ∉ K := by
    intro h
    exact (not_lt_of_ge (compactDensityRadius_bounds K hK z h j)) hz
  simp [conditionedStandardGaussianDensity, conditionedExponentialDensity, hzK]

/-- Explicitly constructs all scalar prefix-conditional densities of the
actual conditioned Gaussian. There is no system-existence hypothesis. -/
noncomputable def conditionedGaussianConditionalSystem (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K) :
    ConditionalDensitySystem M (conditionedStandardGaussianDensity M K) :=
  conditionalDensitySystem_of_bounded_cube (conditionedStandardGaussianDensity M K)
    (measurable_conditionedExponentialDensity volume hK.measurableSet _
      (continuous_gaussianEnergy M).measurable)
    (conditionedExponentialDensity_nonneg volume K _ _ hp)
    (conditionedStandardGaussianDensity_bound M K hp)
    (compactDensityRadius_nonneg K hK)
    (conditionedStandardGaussianDensity_support M hK)
    (integral_conditionedExponentialDensity volume hK.measurableSet _ _ hp)

theorem conditionedGaussianConditionalSystem_law (M : ℕ) {K : Set (Fin M → ℝ)}
    (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K) :
    (conditionedGaussianConditionalSystem M hK hp).law =
      ProbabilityTheory.cond (Literature.standardGaussian M) K :=
  conditionedStandardGaussian_measure_eq_cond M hK.measurableSet hp

theorem conditionedGaussianConditionalSystem_entropy_integrable (M : ℕ)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K)
    (j : Fin M) :
    Integrable ((conditionedGaussianConditionalSystem M hK hp).entropyAt j)
      (conditionedGaussianConditionalSystem M hK hp).law :=
  canonical_conditionalEntropy_integrable
    (measurable_conditionedExponentialDensity volume hK.measurableSet _
      (continuous_gaussianEnergy M).measurable)
    (conditionedExponentialDensity_nonneg volume K _ _ hp)
    (conditionedStandardGaussianDensity_bound M K hp)
    (conditionedStandardGaussianDensity_support M hK) j

noncomputable def gaussianRosenblattConstant (kappa : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) / (4 * Real.exp 1) * Real.exp (-kappa)

theorem gaussianRosenblattConstant_pos (kappa : ℝ) : 0 < gaussianRosenblattConstant kappa := by
  unfold gaussianRosenblattConstant
  positivity

/-- Proposition 6.2's explicit conditioned-Gaussian correlation bound.
The sole entropy input is the classical chain identity for the actual
constructed conditional densities. All scalar entropy, normalization,
system existence and finiteness work is proved in this project. -/
theorem conditionedGaussian_correlation_of_chain (M : ℕ) (hM : 0 < M)
    {K : Set (Fin M → ℝ)} (hK : IsCompact K) (hp : 0 < gaussianConditioningMass M K)
    (kappa : ℝ)
    (hmass : ENNReal.ofReal (Real.exp (-kappa * M)) ≤ Literature.standardGaussian M K)
    (hchain : (∑ j, ∫ z, (conditionedGaussianConditionalSystem M hK hp).entropyAt j z
        ∂(conditionedGaussianConditionalSystem M hK hp).law) =
      densityEntropy volume (conditionedStandardGaussianDensity M K)) :
    gaussianRosenblattConstant kappa * M ≤
      ∑ j, ∫ z, z j * (conditionedGaussianConditionalSystem M hK hp).cdfTransform z j
        ∂(conditionedGaussianConditionalSystem M hK hp).law := by
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hraw := (conditionedGaussianConditionalSystem M hK hp).entropy_correlation_lower_bound hM
    (conditionedGaussianConditionalSystem_entropy_integrable M hK hp) hchain
  have hEnt := conditionedStandardGaussian_entropy_lower_of_probability M hK kappa hmass
  have hdiv : Real.log (2 * Real.pi) / 2 - kappa ≤
      densityEntropy volume (conditionedStandardGaussianDensity M K) / M := by
    apply (le_div_iff₀ hMreal).mpr
    nlinarith
  have hExp := Real.exp_le_exp.mpr hdiv
  have hEq : Real.exp (Real.log (2 * Real.pi) / 2 - kappa) =
      Real.sqrt (2 * Real.pi) * Real.exp (-kappa) := by
    calc
      _ = Real.exp (Real.log (Real.sqrt (2 * Real.pi)) + -kappa) := by
        rw [Real.log_sqrt (by positivity)]
        congr 1
      _ = _ := by rw [Real.exp_add, Real.exp_log (by positivity)]
  rw [hEq] at hExp
  calc
    gaussianRosenblattConstant kappa * M =
        (M : ℝ) * (Real.sqrt (2 * Real.pi) * Real.exp (-kappa)) / (4 * Real.exp 1) := by
      unfold gaussianRosenblattConstant
      ring
    _ ≤ (M : ℝ) * Real.exp (densityEntropy volume (conditionedStandardGaussianDensity M K) / M) /
        (4 * Real.exp 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hExp hMreal.le) (by positivity)
    _ ≤ _ := hraw

/-- Full Proposition 6.2 for the actual conditioned Gaussian law, under
the named classical chain-rule and Rosenblatt literature inputs. All
conditional densities and the transform in this statement are concrete
definitions constructed in this project. -/
theorem conditionedGaussian_rosenblatt_facts (literature : Literature.Assumptions)
    (M : ℕ) (hM : 0 < M) {K : Set (Fin M → ℝ)} (hK : IsCompact K)
    (hp : 0 < gaussianConditioningMass M K) (kappa : ℝ)
    (hmass : ENNReal.ofReal (Real.exp (-kappa * M)) ≤ Literature.standardGaussian M K) :
    let U := (conditionedGaussianConditionalSystem M hK hp).cdfTransform
    Measurable U ∧
      Measure.map U (ProbabilityTheory.cond (Literature.standardGaussian M) K) =
        Measure.pi (fun _ : Fin M => ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1 : ℝ) 1)) ∧
      (∀ j, 0 ≤ ∫ z, z j * U z j ∂ProbabilityTheory.cond (Literature.standardGaussian M) K) ∧
      gaussianRosenblattConstant kappa * M ≤
        ∑ j, ∫ z, z j * U z j ∂ProbabilityTheory.cond (Literature.standardGaussian M) K := by
  let s := conditionedGaussianConditionalSystem M hK hp
  have hlaw : s.law = ProbabilityTheory.cond (Literature.standardGaussian M) K :=
    conditionedGaussianConditionalSystem_law M hK hp
  have hH := conditionedGaussianConditionalSystem_entropy_integrable M hK hp
  have hchain := literature.entropyChain M (conditionedStandardGaussianDensity M K) s hH
  have huniform := literature.rosenblatt M (conditionedStandardGaussianDensity M K) s
  have hnonneg := s.coordinate_correlation_nonneg
  have hcorr := conditionedGaussian_correlation_of_chain M hM hK hp kappa hmass hchain
  rw [hlaw] at huniform hnonneg hcorr
  exact ⟨s.measurable_cdfTransform, huniform, hnonneg, hcorr⟩

end Tusnady
