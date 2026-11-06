import Tusnady.EntropyDensityBounded
import Tusnady.EntropyAggregation

/-!
# Correlation from actual conditional density systems

`ConditionalDensitySystem` records actual scalar densities, prefix
dependence and the general disintegration identity. It has no correlation
or moment lower-bound field. Constructing this system for the conditioned
Gaussian and applying the classical entropy chain rule remain explicit
tasks; there is no global existence axiom in this module.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Tusnady

def densityPrefix {M : ℕ} (j : Fin M) (z : Fin M → ℝ) : Fin j.val → ℝ :=
  fun i => z ⟨i.val, lt_trans i.isLt j.isLt⟩

theorem measurable_densityPrefix {M : ℕ} (j : Fin M) : Measurable (densityPrefix j) := by
  exact Measurable.of_eval fun _ => measurable_pi_apply _

structure ConditionalDensitySystem (M : ℕ) (f : (Fin M → ℝ) → ℝ) where
  joint_measurable : Measurable f
  joint_nonneg : ∀ z, 0 ≤ f z
  joint_integrable : Integrable f
  joint_normalized : (∫ z, f z) = 1
  joint_log_integrable : Integrable (fun z => f z * Real.log (f z))
  joint_support : ∃ R : ℝ, 0 ≤ R ∧ ∀ z (j : Fin M), R < |z j| → f z = 0
  density : (j : Fin M) → (Fin j.val → ℝ) → ℝ → ℝ
  density_measurable : ∀ j, Measurable (fun p : (Fin j.val → ℝ) × ℝ => density j p.1 p.2)
  density_nonneg : ∀ j p y, 0 ≤ density j p y
  density_normalized : ∀ j p, (∫ y, density j p y) = 1
  density_bounded_support : ∀ j p, ∃ C R : ℝ, 0 ≤ R ∧
    (∀ y, density j p y ≤ C) ∧ (∀ y, R < |y| → density j p y = 0)
  disintegration : ∀ (j : Fin M) (q : (Fin j.val → ℝ) × ℝ → ℝ), Measurable q →
    Integrable (fun z => q (densityPrefix j z, z j)) (realDensityMeasure volume f) →
    Integrable (fun z => ∫ y, q (densityPrefix j z, y)
      ∂realDensityMeasure volume (density j (densityPrefix j z))) (realDensityMeasure volume f) ∧
    (∫ z, q (densityPrefix j z, z j) ∂realDensityMeasure volume f) =
      ∫ z, (∫ y, q (densityPrefix j z, y)
        ∂realDensityMeasure volume (density j (densityPrefix j z))) ∂realDensityMeasure volume f

namespace ConditionalDensitySystem

variable {M : ℕ} {f : (Fin M → ℝ) → ℝ} (s : ConditionalDensitySystem M f)

noncomputable def law (_s : ConditionalDensitySystem M f) : Measure (Fin M → ℝ) :=
  realDensityMeasure volume f

instance law_isProbabilityMeasure : IsProbabilityMeasure s.law :=
  isProbabilityMeasure_realDensityMeasure volume f s.joint_measurable s.joint_nonneg
    s.joint_integrable s.joint_normalized

theorem scalar_integrable (j : Fin M) (p : Fin j.val → ℝ) : Integrable (s.density j p) := by
  obtain ⟨C, R, _, hC, hR⟩ := s.density_bounded_support j p
  exact integrable_realDensity_of_bounded_interval (s.density j p)
    ((s.density_measurable j).comp (measurable_const.prodMk measurable_id))
    (s.density_nonneg j p) C R hC hR

theorem scalar_log_integrable (j : Fin M) (p : Fin j.val → ℝ) :
    Integrable (fun y => s.density j p y * Real.log (s.density j p y)) := by
  obtain ⟨C, R, _, hC, hR⟩ := s.density_bounded_support j p
  exact integrable_densityLog_of_bounded_interval (s.density j p)
    ((s.density_measurable j).comp (measurable_const.prodMk measurable_id))
    (s.density_nonneg j p) C R hC hR

theorem scalar_firstMoment_integrable (j : Fin M) (p : Fin j.val → ℝ) :
    Integrable (fun y => s.density j p y * y) := by
  obtain ⟨C, R, hR0, _, hR⟩ := s.density_bounded_support j p
  exact integrable_density_firstMoment_of_supported (s.density j p)
    ((s.density_measurable j).comp (measurable_const.prodMk measurable_id))
    (s.density_nonneg j p) (s.scalar_integrable j p) hR0 hR

noncomputable def entropyAt (j : Fin M) (z : Fin M → ℝ) : ℝ :=
  densityEntropy volume (s.density j (densityPrefix j z))

noncomputable def cdfTransform (z : Fin M → ℝ) (j : Fin M) : ℝ :=
  2 * ProbabilityTheory.cdf (realDensityMeasure volume (s.density j (densityPrefix j z))) (z j) - 1

noncomputable def scalarCorrelation (j : Fin M) (z : Fin M → ℝ) : ℝ :=
  ∫ y, y * (2 * ProbabilityTheory.cdf
    (realDensityMeasure volume (s.density j (densityPrefix j z))) y - 1)
    ∂realDensityMeasure volume (s.density j (densityPrefix j z))

theorem scalar_entropy_bound (j : Fin M) (z : Fin M → ℝ) :
    Real.exp (s.entropyAt j z) ≤ (4 * Real.exp 1) * s.scalarCorrelation j z := by
  have h := density_cdf_correlation_lower_bound (s.density j (densityPrefix j z))
    ((s.density_measurable j).comp (measurable_const.prodMk measurable_id))
    (s.density_nonneg j _) (s.scalar_integrable j _) (s.density_normalized j _)
    (s.scalar_log_integrable j _) (s.scalar_firstMoment_integrable j _)
  have hK : 0 < 4 * Real.exp 1 := by positivity
  have hb := (div_le_iff₀ hK).mp h
  simpa only [entropyAt, scalarCorrelation, mul_comm] using hb

theorem scalarCorrelation_nonneg (j : Fin M) (z : Fin M → ℝ) :
    0 ≤ s.scalarCorrelation j z := by
  let d := s.density j (densityPrefix j z)
  haveI := isProbabilityMeasure_realDensityMeasure volume d
    ((s.density_measurable j).comp (measurable_const.prodMk measurable_id))
    (s.density_nonneg j _) (s.scalar_integrable j _) (s.density_normalized j _)
  haveI : NullSingletonClass (realDensityMeasure volume d) := by
    unfold realDensityMeasure
    infer_instance
  exact cdf_correlation_nonneg (realDensityMeasure volume d)
    ((integrable_realDensityMeasure_iff volume d (fun y => y)
      ((s.density_measurable j).comp (measurable_const.prodMk measurable_id))
      (s.density_nonneg j _)).mpr (s.scalar_firstMoment_integrable j _))

theorem coordinate_integrable (j : Fin M) : Integrable (fun z : Fin M → ℝ => z j) s.law := by
  obtain ⟨R, _, hR⟩ := s.joint_support
  apply (integrable_realDensityMeasure_iff volume f (fun z => z j)
    s.joint_measurable s.joint_nonneg).mpr
  apply (s.joint_integrable.const_mul R).mono'
    (s.joint_measurable.mul (measurable_pi_apply j)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (s.joint_nonneg z)]
    by_cases hz : |z j| ≤ R
    · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hz (s.joint_nonneg z)
    · rw [hR z j (lt_of_not_ge hz)]
      simp

theorem cdfTransform_abs_le_one (z : Fin M → ℝ) (j : Fin M) : |s.cdfTransform z j| ≤ 1 := by
  apply abs_le.mpr
  have hlo := ProbabilityTheory.cdf_nonneg
    (realDensityMeasure volume (s.density j (densityPrefix j z))) (z j)
  have hhi := ProbabilityTheory.cdf_le_one
    (realDensityMeasure volume (s.density j (densityPrefix j z))) (z j)
  unfold cdfTransform
  constructor <;> linarith

theorem correlation_test_measurable (j : Fin M) :
    Measurable (fun p : (Fin j.val → ℝ) × ℝ =>
      p.2 * (2 * ProbabilityTheory.cdf (realDensityMeasure volume (s.density j p.1)) p.2 - 1)) := by
  exact measurable_snd.mul (((measurable_cdf_realDensityMeasure_family (s.density j)
    (s.density_measurable j) (s.density_nonneg j) (s.scalar_integrable j)
    (s.density_normalized j)).const_mul 2).sub_const 1)

theorem measurable_cdfTransform : Measurable s.cdfTransform := by
  apply measurable_pi_lambda
  intro j
  exact ((((measurable_cdf_realDensityMeasure_family (s.density j)
    (s.density_measurable j) (s.density_nonneg j) (s.scalar_integrable j)
    (s.density_normalized j)).comp
      ((measurable_densityPrefix j).prodMk (measurable_pi_apply j))).const_mul 2).sub_const 1)

theorem coordinate_correlation_integrable (j : Fin M) :
    Integrable (fun z => z j * s.cdfTransform z j) s.law := by
  apply (s.coordinate_integrable j).mono
    ((s.correlation_test_measurable j).comp
      ((measurable_densityPrefix j).prodMk (measurable_pi_apply j))).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun z => by
    change |z j * s.cdfTransform z j| ≤ |z j|
    rw [abs_mul]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (s.cdfTransform_abs_le_one z j) (abs_nonneg (z j))

set_option maxHeartbeats 1000000 in
theorem disintegrated_correlation (j : Fin M) :
    Integrable (s.scalarCorrelation j) s.law ∧
      (∫ z, z j * s.cdfTransform z j ∂s.law) = ∫ z, s.scalarCorrelation j z ∂s.law := by
  let q : (Fin j.val → ℝ) × ℝ → ℝ := fun p =>
    p.2 * (2 * ProbabilityTheory.cdf (realDensityMeasure volume (s.density j p.1)) p.2 - 1)
  exact s.disintegration j q (s.correlation_test_measurable j)
    (s.coordinate_correlation_integrable j)

theorem coordinate_correlation_nonneg (j : Fin M) :
    0 ≤ ∫ z, z j * s.cdfTransform z j ∂s.law := by
  rw [(s.disintegrated_correlation j).2]
  exact integral_nonneg fun z => s.scalarCorrelation_nonneg j z

/-- The manuscript's new correlation lower bound, derived from actual
conditional scalar densities. Only the explicit classical chain-rule
integrability and identity are inputs beyond the disintegration system.
Neither a correlation lower bound nor an abstract entropy value is an
input. Constructing the system remains a separate obligation. -/
theorem entropy_correlation_lower_bound (hM : 0 < M)
    (hH : ∀ j, Integrable (s.entropyAt j) s.law)
    (hchain : (∑ j, ∫ z, s.entropyAt j z ∂s.law) = densityEntropy volume f) :
    (M : ℝ) * Real.exp (densityEntropy volume f / M) / (4 * Real.exp 1) ≤
      ∑ j, ∫ z, z j * s.cdfTransform z j ∂s.law := by
  letI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hK : 0 < 4 * Real.exp 1 := by positivity
  have he : ∀ j, Integrable (fun z => Real.exp (s.entropyAt j z)) s.law := by
    intro j
    apply (((s.disintegrated_correlation j).1).const_mul (4 * Real.exp 1)).mono'
      ((hH j).aestronglyMeasurable.aemeasurable.exp).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using s.scalar_entropy_bound j z
  have h := entropy_correlation_aggregation s.entropyAt s.scalarCorrelation hK hH he
    (fun j => (s.disintegrated_correlation j).1)
    (fun j => Filter.Eventually.of_forall fun z => s.scalar_entropy_bound j z) hchain
  simp only [Fintype.card_fin] at h
  have hid : (∑ j, ∫ z, s.scalarCorrelation j z ∂s.law) =
      ∑ j, ∫ z, z j * s.cdfTransform z j ∂s.law := by
    exact Finset.sum_congr rfl fun j _ => (s.disintegrated_correlation j).2.symm
  rwa [hid] at h

end ConditionalDensitySystem
end Tusnady
