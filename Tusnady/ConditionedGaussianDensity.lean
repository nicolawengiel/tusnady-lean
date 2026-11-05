import Tusnady.EntropyDensity
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Probability.ConditionalProbability

/-!
# Entropy of an explicitly conditioned exponential density

The Gaussian specialization uses `constant = M/2 * log(2π)` and the sum
of coordinate squares as `energy`. Both the conditioning mass and the
conditioned density are defined by actual integrals.
-/

open MeasureTheory Set

namespace Tusnady

noncomputable def exponentialKernel {X : Type*} (constant : ℝ) (energy : X → ℝ)
    (x : X) : ℝ := Real.exp (-constant - energy x / 2)

noncomputable def exponentialEventMass {X : Type*} [MeasurableSpace X]
    (base : Measure X) (S : Set X) (constant : ℝ) (energy : X → ℝ) : ℝ :=
  ∫ x in S, exponentialKernel constant energy x ∂base

noncomputable def conditionedExponentialDensity {X : Type*} [MeasurableSpace X]
    (base : Measure X) (S : Set X) (constant : ℝ) (energy : X → ℝ) : X → ℝ :=
  S.indicator (fun x => exponentialKernel constant energy x /
    exponentialEventMass base S constant energy)

theorem conditionedExponentialDensity_nonneg {X : Type*} [MeasurableSpace X]
    (base : Measure X) (S : Set X) (constant : ℝ) (energy : X → ℝ)
    (hp : 0 < exponentialEventMass base S constant energy) (x : X) :
    0 ≤ conditionedExponentialDensity base S constant energy x := by
  classical
  by_cases hx : x ∈ S
  · simp only [conditionedExponentialDensity, indicator_of_mem hx]
    exact div_nonneg (Real.exp_pos _).le hp.le
  · simp [conditionedExponentialDensity, hx]

theorem measurable_conditionedExponentialDensity {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    {energy : X → ℝ} (hE : Measurable energy) :
    Measurable (conditionedExponentialDensity base S constant energy) := by
  unfold conditionedExponentialDensity exponentialKernel
  exact (((measurable_const.sub (hE.div_const 2)).exp).div_const _).indicator hS

theorem integrable_conditionedExponentialDensity {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    (energy : X → ℝ) (hk : IntegrableOn (exponentialKernel constant energy) S base) :
    Integrable (conditionedExponentialDensity base S constant energy) base := by
  change Integrable (S.indicator (fun x => exponentialKernel constant energy x /
    exponentialEventMass base S constant energy)) base
  exact (integrable_indicator_iff hS).mpr (hk.div_const _)

theorem integral_conditionedExponentialDensity {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    (energy : X → ℝ) (hp : 0 < exponentialEventMass base S constant energy) :
    (∫ x, conditionedExponentialDensity base S constant energy x ∂base) = 1 := by
  rw [conditionedExponentialDensity, integral_indicator hS, integral_div]
  exact div_self hp.ne'

/-- The conditioning mass is the actual mass of the event under the
unconditioned density measure. -/
theorem exponentialEventMass_eq_measure {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    (energy : X → ℝ) (hk : IntegrableOn (exponentialKernel constant energy) S base) :
    realDensityMeasure base (exponentialKernel constant energy) S =
      ENNReal.ofReal (exponentialEventMass base S constant energy) := by
  rw [realDensityMeasure, withDensity_apply _ hS, exponentialEventMass]
  exact (ofReal_integral_eq_lintegral_ofReal hk
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)).symm

/-- The concrete conditioned density defines exactly mathlib's
conditional probability measure; the identification is proved rather
than assumed. -/
theorem conditionedExponentialDensity_measure_eq_cond {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    {energy : X → ℝ} (hE : Measurable energy)
    (hp : 0 < exponentialEventMass base S constant energy)
    (hk : IntegrableOn (exponentialKernel constant energy) S base) :
    realDensityMeasure base (conditionedExponentialDensity base S constant energy) =
      ProbabilityTheory.cond (realDensityMeasure base (exponentialKernel constant energy)) S := by
  classical
  have hm := exponentialEventMass_eq_measure base hS constant energy hk
  have hkernel : Measurable (fun x => ENNReal.ofReal (exponentialKernel constant energy x)) := by
    unfold exponentialKernel
    fun_prop
  have hrepr : (fun x => ENNReal.ofReal (conditionedExponentialDensity base S constant energy x)) =
      (ENNReal.ofReal (exponentialEventMass base S constant energy))⁻¹ •
        S.indicator (fun x => ENNReal.ofReal (exponentialKernel constant energy x)) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [conditionedExponentialDensity, indicator_of_mem hx, Pi.smul_apply, smul_eq_mul]
      rw [ENNReal.ofReal_div_of_pos hp, div_eq_mul_inv, mul_comm]
    · simp [conditionedExponentialDensity, hx]
  rw [ProbabilityTheory.cond, hm]
  unfold realDensityMeasure
  rw [hrepr, withDensity_smul _ (hkernel.indicator hS), withDensity_indicator hS,
    restrict_withDensity hS]

theorem conditionedExponentialDensity_log_identity {X : Type*} [MeasurableSpace X]
    (base : Measure X) (S : Set X) (constant : ℝ) (energy : X → ℝ)
    (hp : 0 < exponentialEventMass base S constant energy) (x : X) :
    let f := conditionedExponentialDensity base S constant energy
    f x * Real.log (f x) = -constant * f x - (1 / 2 : ℝ) * (f x * energy x) -
      Real.log (exponentialEventMass base S constant energy) * f x := by
  classical
  dsimp only
  by_cases hx : x ∈ S
  · simp only [conditionedExponentialDensity, indicator_of_mem hx]
    simp only [exponentialKernel]
    rw [Real.log_div (Real.exp_ne_zero _) hp.ne', Real.log_exp]
    ring
  · simp [conditionedExponentialDensity, hx]

/-- The entropy integrand of the conditioned density is genuinely
integrable, rather than merely assigned a default Bochner integral. -/
theorem integrable_conditionedExponentialDensity_log {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    (energy : X → ℝ) (hp : 0 < exponentialEventMass base S constant energy)
    (hk : IntegrableOn (exponentialKernel constant energy) S base)
    (hm : Integrable (fun x => conditionedExponentialDensity base S constant energy x *
      energy x) base) :
    Integrable (fun x => conditionedExponentialDensity base S constant energy x *
      Real.log (conditionedExponentialDensity base S constant energy x)) base := by
  have hi := integrable_conditionedExponentialDensity base hS constant energy hk
  have hlin := ((hi.const_mul (-constant)).sub (hm.const_mul (1 / 2 : ℝ))).sub
    (hi.const_mul (Real.log (exponentialEventMass base S constant energy)))
  apply hlin.congr
  exact Filter.Eventually.of_forall fun x =>
    (conditionedExponentialDensity_log_identity base S constant energy hp x).symm

/-- Exact entropy formula for the actual conditioned density.
The weighted energy moment is the only extra integrability input. -/
theorem conditionedExponentialDensity_entropy_eq {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    (energy : X → ℝ) (hp : 0 < exponentialEventMass base S constant energy)
    (hk : IntegrableOn (exponentialKernel constant energy) S base)
    (hm : Integrable (fun x => conditionedExponentialDensity base S constant energy x *
      energy x) base) :
    densityEntropy base (conditionedExponentialDensity base S constant energy) =
      constant + (1 / 2 : ℝ) *
        (∫ x, conditionedExponentialDensity base S constant energy x * energy x ∂base) +
      Real.log (exponentialEventMass base S constant energy) := by
  let f := conditionedExponentialDensity base S constant energy
  have hfi : Integrable f base := integrable_conditionedExponentialDensity base hS constant energy hk
  have hfnorm : (∫ x, f x ∂base) = 1 :=
    integral_conditionedExponentialDensity base hS constant energy hp
  have hpoint := conditionedExponentialDensity_log_identity base S constant energy hp
  have heval : (∫ x, f x * Real.log (f x) ∂base) =
      -constant * (∫ x, f x ∂base) - (1 / 2 : ℝ) * (∫ x, f x * energy x ∂base) -
        Real.log (exponentialEventMass base S constant energy) * (∫ x, f x ∂base) := by
    simp_rw [show ∀ x, f x * Real.log (f x) = -constant * f x -
      (1 / 2 : ℝ) * (f x * energy x) -
      Real.log (exponentialEventMass base S constant energy) * f x from hpoint]
    rw [integral_sub (f := fun x => -constant * f x - (1 / 2 : ℝ) * (f x * energy x))
      (g := fun x => Real.log (exponentialEventMass base S constant energy) * f x)
      ((hfi.const_mul _).sub (hm.const_mul _)) (hfi.const_mul _),
      integral_sub (f := fun x => -constant * f x)
        (g := fun x => (1 / 2 : ℝ) * (f x * energy x)) (hfi.const_mul _) (hm.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  unfold densityEntropy
  change -(∫ x, f x * Real.log (f x) ∂base) = _
  rw [heval, hfnorm]
  ring

/-- Lower entropy bound used in (6.3), with nonnegative energy. -/
theorem conditionedExponentialDensity_entropy_lower {X : Type*} [MeasurableSpace X]
    (base : Measure X) {S : Set X} (hS : MeasurableSet S) (constant : ℝ)
    (energy : X → ℝ) (hp : 0 < exponentialEventMass base S constant energy)
    (hk : IntegrableOn (exponentialKernel constant energy) S base)
    (hm : Integrable (fun x => conditionedExponentialDensity base S constant energy x *
      energy x) base) (hE : ∀ x, 0 ≤ energy x) :
    constant + Real.log (exponentialEventMass base S constant energy) ≤
      densityEntropy base (conditionedExponentialDensity base S constant energy) := by
  rw [conditionedExponentialDensity_entropy_eq base hS constant energy hp hk hm]
  have hmpos : 0 ≤ ∫ x, conditionedExponentialDensity base S constant energy x * energy x ∂base := by
    apply integral_nonneg
    intro x
    exact mul_nonneg (conditionedExponentialDensity_nonneg base S constant energy hp x) (hE x)
  linarith

theorem continuous_exponentialKernel {X : Type*} [TopologicalSpace X]
    (constant : ℝ) {energy : X → ℝ} (hE : Continuous energy) :
    Continuous (exponentialKernel constant energy) := by
  unfold exponentialKernel
  fun_prop

/-- Compact conditioning makes the energy moment integrable without a
separate moment assumption. -/
theorem integrable_conditionedEnergy_of_isCompact {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    (base : Measure X) [IsFiniteMeasureOnCompacts base]
    {S : Set X} (hS : IsCompact S) (constant : ℝ) {energy : X → ℝ}
    (hE : Continuous energy) :
    Integrable (fun x => conditionedExponentialDensity base S constant energy x * energy x) base := by
  classical
  have hkE : IntegrableOn (fun x => exponentialKernel constant energy x * energy x) S base :=
    ((continuous_exponentialKernel constant hE).mul hE).continuousOn.integrableOn_compact hS
  have hid : (fun x => conditionedExponentialDensity base S constant energy x * energy x) =
      S.indicator (fun x => (exponentialKernel constant energy x * energy x) /
        exponentialEventMass base S constant energy) := by
    funext x
    by_cases hx : x ∈ S
    · simp only [conditionedExponentialDensity, indicator_of_mem hx]
      ring
    · simp [conditionedExponentialDensity, hx]
  rw [hid]
  exact (integrable_indicator_iff hS.measurableSet).mpr (hkE.div_const _)

/-- The actual entropy formula on a compact conditioning event. There is
no unproved integrability/entropy assertion among its inputs. -/
theorem conditionedExponentialDensity_entropy_eq_of_isCompact {X : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [T2Space X]
    (base : Measure X) [IsFiniteMeasureOnCompacts base]
    {S : Set X} (hS : IsCompact S) (constant : ℝ) {energy : X → ℝ}
    (hE : Continuous energy) (hp : 0 < exponentialEventMass base S constant energy) :
    densityEntropy base (conditionedExponentialDensity base S constant energy) =
      constant + (1 / 2 : ℝ) *
        (∫ x, conditionedExponentialDensity base S constant energy x * energy x ∂base) +
      Real.log (exponentialEventMass base S constant energy) := by
  exact conditionedExponentialDensity_entropy_eq base hS.measurableSet constant energy hp
    ((continuous_exponentialKernel constant hE).continuousOn.integrableOn_compact hS)
    (integrable_conditionedEnergy_of_isCompact base hS constant hE)

end Tusnady
