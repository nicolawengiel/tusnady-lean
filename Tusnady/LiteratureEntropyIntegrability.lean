import Tusnady.LiteratureEntropyDisintegration

/-! # Actual conditional-log integrability from conditional entropy

The compact joint support bounds the integrated negative part of each
conditional log-density. Integrable conditional entropies then control
the full absolute conditional log integral.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Tusnady.LiteratureProof
set_option maxHeartbeats 1000000

theorem density_negLogPart_le_one {x : ℝ} (hx : 0 ≤ x) : max (-(x * Real.log x)) 0 ≤ 1 := by
  have h := density_gibbs_pointwise (f := x) (g := 1) hx (by norm_num)
  simp only [Real.log_one, mul_zero, sub_zero] at h
  exact max_le (by linarith) (by norm_num)

theorem conditional_density_negativePart_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    Integrable (fun p : (Fin j.val → ℝ) × ℝ =>
      max (-(s.density j p.1 p.2 * Real.log (s.density j p.1 p.2))) 0)
      ((actualPrefixLaw s j).prod volume) := by
  obtain ⟨R, hR, hsupport⟩ := s.joint_support
  have hz : ∀ᵐ z ∂s.law, |z j| ≤ R := by
    change ∀ᵐ z ∂volume.withDensity (fun z => ENNReal.ofReal (f z)), |z j| ≤ R
    apply (ae_withDensity_iff s.joint_measurable.ennreal_ofReal).mpr
    exact Filter.Eventually.of_forall fun z hf => by
      by_contra h
      exact hf (by rw [hsupport z j (lt_of_not_ge h)]; simp)
  have hp : ∀ᵐ p ∂actualConditionalPairLaw s j, |p.2| ≤ R := by
    rw [← actual_prefix_pair_law]
    exact (ae_map_iff ((measurable_densityPrefix j).prodMk (measurable_pi_apply j)).aemeasurable
      (isClosed_le continuous_snd.abs continuous_const).measurableSet).mpr hz
  have hbase : ∀ᵐ p ∂(actualPrefixLaw s j).prod volume,
      ENNReal.ofReal (s.density j p.1 p.2) ≠ 0 → |p.2| ≤ R :=
    (ae_withDensity_iff (s.density_measurable j).ennreal_ofReal).mp hp
  have hRint : Integrable ((Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ))) := by
    apply (integrable_indicator_iff measurableSet_Icc).mpr
    exact (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn.integrableOn_compact isCompact_Icc
  have hdom : Integrable (fun p : (Fin j.val → ℝ) × ℝ =>
      (Icc (-R) R).indicator (fun _ : ℝ => (1 : ℝ)) p.2) ((actualPrefixLaw s j).prod volume) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Fin j.val → ℝ => (1 : ℝ)) (actualPrefixLaw s j)).mul_prod hRint
  apply hdom.mono'
    (((s.density_measurable j).mul (s.density_measurable j).log).neg.max measurable_const).aestronglyMeasurable
  filter_upwards [hbase] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  by_cases hy : p.2 ∈ Icc (-R) R
  · rw [Set.indicator_of_mem hy]
    exact density_negLogPart_le_one (s.density_nonneg j p.1 p.2)
  · rw [Set.indicator_of_notMem hy]
    have hd : s.density j p.1 p.2 = 0 := by
      by_contra hd
      have hpos : 0 < s.density j p.1 p.2 := lt_of_le_of_ne (s.density_nonneg j p.1 p.2) (Ne.symm hd)
      exact hy (abs_le.mp (hp (ENNReal.ofReal_pos.mpr hpos).ne'))
    simp [hd]

theorem abs_eq_add_twice_negativePart (x : ℝ) : |x| = x + 2 * max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_right (neg_nonpos.mpr hx)]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

theorem conditional_density_log_joint_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M)
    (hH : Integrable (s.entropyAt j) s.law) :
    Integrable (fun p : (Fin j.val → ℝ) × ℝ =>
      s.density j p.1 p.2 * Real.log (s.density j p.1 p.2))
      ((actualPrefixLaw s j).prod volume) := by
  let H : (Fin j.val → ℝ) → ℝ := fun p => densityEntropy volume (s.density j p)
  have hHm : Measurable H := by
    exact ((s.density_measurable j).mul (s.density_measurable j).log).stronglyMeasurable.integral_prod_right'.neg.measurable
  have hHi : Integrable H (actualPrefixLaw s j) :=
    (integrable_map_measure hHm.aestronglyMeasurable (measurable_densityPrefix j).aemeasurable).mpr hH
  have hN := conditional_density_negativePart_integrable s j
  have hinner (p : Fin j.val → ℝ) :
      (∫ y, ‖s.density j p y * Real.log (s.density j p y)‖) = -H p +
        2 * ∫ y, max (-(s.density j p y * Real.log (s.density j p y))) 0 := by
    simp_rw [Real.norm_eq_abs, abs_eq_add_twice_negativePart]
    rw [integral_add (s.scalar_log_integrable j p) ((s.scalar_log_integrable j p).neg_part.const_mul 2),
      integral_const_mul]
    simp only [H, densityEntropy, neg_neg]
  apply (integrable_prod_iff
    ((s.density_measurable j).mul (s.density_measurable j).log).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (s.scalar_log_integrable j), ?_⟩
  change Integrable (fun p => ∫ y, ‖s.density j p y * Real.log (s.density j p y)‖) (actualPrefixLaw s j)
  simp_rw [hinner]
  exact hHi.neg.add (hN.integral_prod_left.const_mul 2)

def conditionalLogDensity {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (z : Fin M → ℝ) : ℝ :=
  Real.log (s.density j (densityPrefix j z) (z j))

theorem conditionalLogDensity_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M)
    (hH : Integrable (s.entropyAt j) s.law) : Integrable (conditionalLogDensity s j) s.law := by
  have hpair : Integrable (fun p : (Fin j.val → ℝ) × ℝ => Real.log (s.density j p.1 p.2))
      (actualConditionalPairLaw s j) :=
    (integrable_realDensityMeasure_iff _ _ _ (s.density_measurable j)
      (fun p => s.density_nonneg j p.1 p.2)).mpr (conditional_density_log_joint_integrable s j hH)
  rw [← actual_prefix_pair_law] at hpair
  exact (integrable_map_measure (s.density_measurable j).log.aestronglyMeasurable
    ((measurable_densityPrefix j).prodMk (measurable_pi_apply j)).aemeasurable).mp hpair

theorem integral_conditionalLogDensity {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M)
    (hH : Integrable (s.entropyAt j) s.law) :
    (∫ z, conditionalLogDensity s j z ∂s.law) = -(∫ z, s.entropyAt j z ∂s.law) := by
  have hdis := (s.disintegration j (fun p => Real.log (s.density j p.1 p.2))
    (s.density_measurable j).log (conditionalLogDensity_integrable s j hH)).2
  have hinner (p : Fin j.val → ℝ) :
      (∫ y, Real.log (s.density j p y) ∂realDensityMeasure volume (s.density j p)) =
        -densityEntropy volume (s.density j p) := by
    rw [integral_realDensityMeasure volume (s.density j p) _
      ((s.density_measurable j).comp (measurable_const.prodMk measurable_id)) (s.density_nonneg j p)]
    simp only [densityEntropy, neg_neg]
  simp_rw [hinner] at hdis
  rw [integral_neg] at hdis
  exact hdis

end Tusnady.LiteratureProof
