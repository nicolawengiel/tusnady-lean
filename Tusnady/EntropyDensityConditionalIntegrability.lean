import Tusnady.EntropyDensitySystemConstruction
import Tusnady.EntropyDensityScaling

/-! # Finiteness of the actual conditional entropy integrals -/

open MeasureTheory Set

namespace Tusnady

theorem prefixCoordinateSplit_symm_prefix {M : ℕ} (j : Fin M)
    (p : (Fin j.val → ℝ) × ℝ) (t : DensityTail M (j.val + 1)) :
    densityPrefix j ((prefixCoordinateSplit j).symm (p, t)) = p.1 := by
  have h := congrArg (fun w => w.1.1) ((prefixCoordinateSplit j).apply_symm_apply (p, t))
  dsimp only at h
  rw [prefixCoordinateSplit_fst] at h
  exact h

theorem prefixPairDensity_zero_prefix {M : ℕ} {f : (Fin M → ℝ) → ℝ} {R : ℝ}
    (hsupport : ∀ z (i : Fin M), R < |z i| → f z = 0) (j : Fin M)
    (p : Fin j.val → ℝ) (y : ℝ) (i : Fin j.val) (hi : R < |p i|) :
    prefixPairDensity f j (p, y) = 0 := by
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun t => by
    apply hsupport _ ⟨i.val, lt_trans i.isLt j.isLt⟩
    have h := congrArg (fun v => v i) (prefixCoordinateSplit_symm_prefix j (p, y) t)
    change densityPrefix j ((prefixCoordinateSplit j).symm ((p, y), t)) i = p i at h
    change R < |densityPrefix j ((prefixCoordinateSplit j).symm ((p, y), t)) i|
    rwa [h]

theorem prefixPairDensity_zero_outside_cube {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) {C R : ℝ} (hC : ∀ z, f z ≤ C)
    (hsupport : ∀ z (i : Fin M), R < |z i| → f z = 0) (j : Fin M) :
    ∀ p, p ∉ (Icc (fun _ => -R) (fun _ => R)) ×ˢ Icc (-R) R →
      prefixPairDensity f j p = 0 := by
  intro p hp
  by_cases hprefix : p.1 ∈ Icc (fun _ => -R) (fun _ => R)
  · have hy : p.2 ∉ Icc (-R) R := fun h => hp ⟨hprefix, h⟩
    have hyR : R < |p.2| := lt_of_not_ge (fun h => hy (abs_le.mp h))
    obtain ⟨_, _, hzero⟩ := prefixPairDensity_bounded_support hfm hf hC hsupport j
    exact hzero p.1 p.2 hyR
  · have hnot : ¬∀ i, |p.1 i| ≤ R := by
      intro hall
      exact hprefix ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩
    push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    exact prefixPairDensity_zero_prefix hsupport j p.1 p.2 i hi

theorem prefixPairDensityLog_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) {C R : ℝ} (hC : ∀ z, f z ≤ C)
    (hsupport : ∀ z (i : Fin M), R < |z i| → f z = 0) (j : Fin M) :
    Integrable (fun p => prefixPairDensity f j p * Real.log (prefixPairDensity f j p)) := by
  obtain ⟨C', hC', _⟩ := prefixPairDensity_bounded_support hfm hf hC hsupport j
  exact integrable_mul_log_of_bounded_supported volume (prefixPairDensity f j)
    (measurableSet_Icc.prod measurableSet_Icc) (isCompact_Icc.prod isCompact_Icc).measure_lt_top
    (prefixPairDensity_measurable hfm j) (prefixPairDensity_nonneg hf j) C'
    (fun p => hC' p.1 p.2) (prefixPairDensity_zero_outside_cube hfm hf hC hsupport j)

theorem prefixMarginalDensityLog_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) {C R : ℝ} (hC : ∀ z, f z ≤ C)
    (hsupport : ∀ z (i : Fin M), R < |z i| → f z = 0) (j : Fin M) :
    Integrable (fun p => productDensityMarginal (prefixPairDensity f j) p *
      Real.log (productDensityMarginal (prefixPairDensity f j) p)) := by
  let g := prefixPairDensity f j
  obtain ⟨C', hC', hR'⟩ := prefixPairDensity_bounded_support hfm hf hC hsupport j
  have hgm : Measurable g := prefixPairDensity_measurable hfm j
  have hg : ∀ p, 0 ≤ g p := prefixPairDensity_nonneg hf j
  have hm : ∀ p, 0 ≤ productDensityMarginal g p := fun p => integral_nonneg fun y => hg (p, y)
  have hmbound (p : Fin j.val → ℝ) : productDensityMarginal g p ≤
      (volume : Measure ℝ).real (Icc (-R) R) * C' := by
    exact integratedDensity_bound_of_supported volume g hgm hg measurableSet_Icc
      isCompact_Icc.measure_lt_top C' hC' (fun p y hy => hR' p y (lt_of_not_ge (fun h => hy (abs_le.mp h)))) p
  apply integrable_mul_log_of_bounded_supported volume (productDensityMarginal g)
    measurableSet_Icc isCompact_Icc.measure_lt_top (productDensityMarginal_measurable hgm) hm
    ((volume : Measure ℝ).real (Icc (-R) R) * C') hmbound
  intro p hp
  have hnot : ¬∀ i, |p i| ≤ R := by
    intro hall
    exact hp ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩
  push_neg at hnot
  obtain ⟨i, hi⟩ := hnot
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun y => prefixPairDensity_zero_prefix hsupport j p y i hi

/-- Integrability of every actual conditional entropy at a prefix, with
all finiteness established from bounds on the original joint density. -/
theorem canonical_conditionalEntropy_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) {C R : ℝ} (hC : ∀ z, f z ≤ C)
    (hsupport : ∀ z (i : Fin M), R < |z i| → f z = 0) (j : Fin M) :
    Integrable (fun z => densityEntropy volume
      (productConditionalDensity (prefixPairDensity f j) (densityPrefix j z)))
      (realDensityMeasure volume f) := by
  let μ := realDensityMeasure volume f
  let g := prefixPairDensity f j
  have hfi := integrable_jointDensity_of_bounded_cube hfm hf hC hsupport
  have hgm : Measurable g := prefixPairDensity_measurable hfm j
  have hg : ∀ p, 0 ≤ g p := prefixPairDensity_nonneg hf j
  have hgi : Integrable g := prefixPairDensity_integrable hfi j
  obtain ⟨C', hC', hR'⟩ := prefixPairDensity_bounded_support hfm hf hC hsupport j
  have hslice : ∀ p, Integrable (fun y => g (p, y)) := by
    intro p
    exact integrable_realDensity_of_bounded_interval (fun y => g (p, y))
      (hgm.comp (measurable_const.prodMk measurable_id)) (fun y => hg (p, y)) C' R (hC' p) (hR' p)
  have hsliceLog : ∀ p, Integrable (fun y => g (p, y) * Real.log (g (p, y))) := by
    intro p
    exact integrable_densityLog_of_bounded_interval (fun y => g (p, y))
      (hgm.comp (measurable_const.prodMk measurable_id)) (fun y => hg (p, y)) C' R (hC' p) (hR' p)
  have hcond := productConditionalDensity_entropy_integrable volume g hgm hg hslice hsliceLog
    (prefixPairDensityLog_integrable hfm hf hC hsupport j)
    (prefixMarginalDensityLog_integrable hfm hf hC hsupport j)
  have hprefix : μ.map (densityPrefix j) = realDensityMeasure volume (productDensityMarginal g) := by
    calc
      _ = (μ.map (fun z => (densityPrefix j z, z j))).map Prod.fst := by
        rw [Measure.map_map measurable_fst
          ((measurable_densityPrefix j).prodMk (measurable_pi_apply j))]
        rfl
      _ = (realDensityMeasure volume g).map Prod.fst := by rw [prefixPairDensity_map hf hfi j]
      _ = _ := productDensityMarginal_map_fst volume g hgm hg hgi
  have hmap : Integrable (fun p => densityEntropy volume (productConditionalDensity g p))
      (μ.map (densityPrefix j)) := by
    rw [hprefix]
    exact hcond
  exact (integrable_map_measure hmap.aestronglyMeasurable
    (measurable_densityPrefix j).aemeasurable).mp hmap

theorem bounded_cube_system_entropy_integrable {M : ℕ}
    (f : (Fin M → ℝ) → ℝ) (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    {C R : ℝ} (hC : ∀ z, f z ≤ C) (hR : 0 ≤ R)
    (hsupport : ∀ z (j : Fin M), R < |z j| → f z = 0) (hnorm : (∫ z, f z) = 1)
    (j : Fin M) :
    Integrable ((conditionalDensitySystem_of_bounded_cube f hfm hf hC hR hsupport hnorm).entropyAt j)
      (conditionalDensitySystem_of_bounded_cube f hfm hf hC hR hsupport hnorm).law :=
  canonical_conditionalEntropy_integrable hfm hf hC hsupport j

end Tusnady
