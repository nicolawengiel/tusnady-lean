import Tusnady.Literature
import Tusnady.EntropyDensityDisintegration

/-! # Actual prefix-pair density laws from the general disintegration data

This is a measure identity, not a new disintegration assumption. It is a
foundation for proving the differential entropy chain identity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Tusnady.LiteratureProof

def actualPrefixLaw {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) : Measure (Fin j.val → ℝ) :=
  s.law.map (densityPrefix j)

instance actualPrefixLaw_probability {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) : IsProbabilityMeasure (actualPrefixLaw s j) :=
  Measure.isProbabilityMeasure_map (measurable_densityPrefix j).aemeasurable

theorem conditionalDensity_joint_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    Integrable (fun p : (Fin j.val → ℝ) × ℝ => s.density j p.1 p.2)
      ((actualPrefixLaw s j).prod volume) := by
  apply (integrable_prod_iff (s.density_measurable j).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (s.scalar_integrable j), ?_⟩
  have heq (p : Fin j.val → ℝ) : (∫ y, ‖s.density j p y‖) = 1 := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (s.density_nonneg j p _)]
    exact s.density_normalized j p
  simp_rw [heq]
  exact integrable_const 1

def actualConditionalPairLaw {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) : Measure ((Fin j.val → ℝ) × ℝ) :=
  realDensityMeasure ((actualPrefixLaw s j).prod volume) (fun p => s.density j p.1 p.2)

theorem conditionalDensity_joint_normalized {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    (∫ p, s.density j p.1 p.2 ∂(actualPrefixLaw s j).prod volume) = 1 := by
  rw [integral_prod _ (conditionalDensity_joint_integrable s j)]
  simp_rw [s.density_normalized j]
  simp

instance actualConditionalPairLaw_probability {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) : IsProbabilityMeasure (actualConditionalPairLaw s j) :=
  isProbabilityMeasure_realDensityMeasure _ _ (s.density_measurable j)
    (fun p => s.density_nonneg j p.1 p.2) (conditionalDensity_joint_integrable s j)
    (conditionalDensity_joint_normalized s j)

/-- The full actual prefix-coordinate distribution equals its actual
prefix law multiplied by the recorded conditional scalar density. -/
theorem actual_prefix_pair_law {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    s.law.map (fun z => (densityPrefix j z, z j)) = actualConditionalPairLaw s j := by
  apply Measure.ext
  intro A hA
  let g : ((Fin j.val → ℝ) × ℝ) → ℝ := fun p => s.density j p.1 p.2
  let q : ((Fin j.val → ℝ) × ℝ) → ℝ := A.indicator (fun _ => 1)
  let h : (Fin j.val → ℝ) → ℝ := fun p => ∫ y, A.indicator g (p,y)
  have hgm : Measurable g := s.density_measurable j
  have hgi := conditionalDensity_joint_integrable s j
  have hqm : Measurable q := measurable_const.indicator hA
  have hqi : Integrable (fun z => q (densityPrefix j z, z j)) s.law := by
    apply Integrable.of_bound
      (hqm.comp ((measurable_densityPrefix j).prodMk (measurable_pi_apply j))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun z => by
      dsimp [q]
      by_cases hz : (densityPrefix j z, z j) ∈ A <;> simp [hz]
  have h_inner (p : Fin j.val → ℝ) :
      (∫ y, q (p,y) ∂realDensityMeasure volume (s.density j p)) = h p := by
    rw [integral_realDensityMeasure volume (s.density j p) (fun y => q (p,y))
      ((s.density_measurable j).comp (measurable_const.prodMk measurable_id)) (s.density_nonneg j p)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      by_cases hy : (p,y) ∈ A <;> simp [q, g, hy]
  have hh_m : Measurable h := (hgm.indicator hA).stronglyMeasurable.integral_prod_right'.measurable
  have hdis := (s.disintegration j q hqm hqi).2
  change (∫ z, q (densityPrefix j z, z j) ∂s.law) =
    ∫ z, (∫ y, q (densityPrefix j z, y) ∂realDensityMeasure volume (s.density j (densityPrefix j z)))
      ∂s.law at hdis
  simp_rw [h_inner] at hdis
  have hmap : (∫ p, h p ∂actualPrefixLaw s j) = ∫ z, h (densityPrefix j z) ∂s.law :=
    integral_map (measurable_densityPrefix j).aemeasurable hh_m.aestronglyMeasurable
  have hfubini : (∫ p in A, g p ∂(actualPrefixLaw s j).prod volume) =
      ∫ p, h p ∂actualPrefixLaw s j := by
    rw [← integral_indicator hA, integral_prod _ (hgi.indicator hA)]
  have hpre : MeasurableSet ((fun z => (densityPrefix j z, z j)) ⁻¹' A) :=
    hA.preimage ((measurable_densityPrefix j).prodMk (measurable_pi_apply j))
  have hleft : (∫ z, q (densityPrefix j z, z j) ∂s.law) =
      s.law.real ((fun z => (densityPrefix j z, z j)) ⁻¹' A) := by
    have hpoint : (fun z => q (densityPrefix j z, z j)) =
        (((fun z => (densityPrefix j z, z j)) ⁻¹' A).indicator (fun _ => (1 : ℝ))) := by
      funext z
      by_cases hz : (densityPrefix j z, z j) ∈ A <;> simp [q, hz]
    rw [hpoint]
    exact integral_indicator_one hpre
  rw [hleft, ← hmap, ← hfubini] at hdis
  rw [Measure.map_apply ((measurable_densityPrefix j).prodMk (measurable_pi_apply j)) hA,
    actualConditionalPairLaw, realDensityMeasure_apply _ _
      (fun p => s.density_nonneg j p.1 p.2) hgi hA]
  rw [← hdis, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top s.law _)]

end Tusnady.LiteratureProof
