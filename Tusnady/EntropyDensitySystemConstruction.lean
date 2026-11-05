import Tusnady.EntropyDensityMarginal

/-!
# Construction of conditional density systems from actual joint densities

The density at each prefix is the quotient of the explicit pair marginal
by its scalar marginal. Zero marginals use the proved null-prefix fallback.
-/

open MeasureTheory Set

namespace Tusnady

theorem densityCube_zero {M : ℕ} {f : (Fin M → ℝ) → ℝ} {R : ℝ}
    (hsupport : ∀ z (j : Fin M), R < |z j| → f z = 0) :
    ∀ z, z ∉ Icc (fun _ => -R) (fun _ => R) → f z = 0 := by
  intro z hz
  have hnot : ¬∀ j, |z j| ≤ R := by
    intro hall
    exact hz ⟨fun j => (abs_le.mp (hall j)).1, fun j => (abs_le.mp (hall j)).2⟩
  push_neg at hnot
  obtain ⟨j, hj⟩ := hnot
  exact hsupport z j hj

theorem integrable_jointDensity_of_bounded_cube {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) {C R : ℝ} (hC : ∀ z, f z ≤ C)
    (hsupport : ∀ z (j : Fin M), R < |z j| → f z = 0) : Integrable f := by
  apply integrable_of_bounded_supported volume f measurableSet_Icc isCompact_Icc.measure_lt_top hfm C
  · intro z
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf z)] using hC z
  · exact densityCube_zero hsupport

theorem integrable_jointDensityLog_of_bounded_cube {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) {C R : ℝ} (hC : ∀ z, f z ≤ C)
    (hsupport : ∀ z (j : Fin M), R < |z j| → f z = 0) :
    Integrable (fun z => f z * Real.log (f z)) := by
  exact integrable_mul_log_of_bounded_supported volume f measurableSet_Icc
    isCompact_Icc.measure_lt_top hfm hf C hC (densityCube_zero hsupport)

/-- General disintegration for the concrete prefix-conditional quotient.
The two pushforward identities are supplied by proved marginal lemmas. -/
theorem prefixConditionalDensity_disintegrate {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) (hfi : Integrable f)
    {C R : ℝ} (hC : ∀ z, f z ≤ C)
    (hsupport : ∀ z (j : Fin M), R < |z j| → f z = 0)
    (j : Fin M) (q : (Fin j.val → ℝ) × ℝ → ℝ) (hqm : Measurable q)
    (hq : Integrable (fun z => q (densityPrefix j z, z j)) (realDensityMeasure volume f)) :
    Integrable (fun z => ∫ y, q (densityPrefix j z, y)
      ∂realDensityMeasure volume (productConditionalDensity (prefixPairDensity f j) (densityPrefix j z)))
      (realDensityMeasure volume f) ∧
    (∫ z, q (densityPrefix j z, z j) ∂realDensityMeasure volume f) =
      ∫ z, (∫ y, q (densityPrefix j z, y)
        ∂realDensityMeasure volume (productConditionalDensity (prefixPairDensity f j) (densityPrefix j z)))
        ∂realDensityMeasure volume f := by
  let μ := realDensityMeasure volume f
  let g := prefixPairDensity f j
  let pairMap : (Fin M → ℝ) → (Fin j.val → ℝ) × ℝ := fun z => (densityPrefix j z, z j)
  have hpairm : Measurable pairMap := (measurable_densityPrefix j).prodMk (measurable_pi_apply j)
  have hpair : μ.map pairMap = realDensityMeasure volume g := prefixPairDensity_map hf hfi j
  have hgm : Measurable g := prefixPairDensity_measurable hfm j
  have hg : ∀ p, 0 ≤ g p := prefixPairDensity_nonneg hf j
  have hgi : Integrable g := prefixPairDensity_integrable hfi j
  obtain ⟨C', hC', hR'⟩ := prefixPairDensity_bounded_support hfm hf hC hsupport j
  have hslice : ∀ p, Integrable (fun y => g (p, y)) := by
    intro p
    exact integrable_realDensity_of_bounded_interval (fun y => g (p, y))
      (hgm.comp (measurable_const.prodMk measurable_id)) (fun y => hg (p, y)) C' R (hC' p) (hR' p)
  have hqMap : Integrable q (realDensityMeasure volume g) := by
    rw [← hpair]
    exact (integrable_map_measure hqm.aestronglyMeasurable hpairm.aemeasurable).mpr hq
  have hdis := productConditionalDensity_disintegrate volume g hgm hg hslice q hqMap
  let innerIntegral : (Fin j.val → ℝ) → ℝ := fun p =>
    ∫ y, q (p, y) ∂realDensityMeasure volume (productConditionalDensity g p)
  have hprefix : μ.map (densityPrefix j) = realDensityMeasure volume (productDensityMarginal g) := by
    calc
      _ = (μ.map pairMap).map Prod.fst := by
        rw [Measure.map_map measurable_fst hpairm]
        rfl
      _ = (realDensityMeasure volume g).map Prod.fst := by rw [hpair]
      _ = _ := productDensityMarginal_map_fst volume g hgm hg hgi
  have hInnerMap : Integrable innerIntegral (μ.map (densityPrefix j)) := by
    rw [hprefix]
    exact hdis.1
  have hInnerOriginal : Integrable (fun z => innerIntegral (densityPrefix j z)) μ :=
    (integrable_map_measure hInnerMap.aestronglyMeasurable
      (measurable_densityPrefix j).aemeasurable).mp hInnerMap
  constructor
  · exact hInnerOriginal
  · calc
      _ = ∫ p, q p ∂realDensityMeasure volume g := by
        rw [← hpair]
        exact (integral_map hpairm.aemeasurable hqm.aestronglyMeasurable).symm
      _ = ∫ p, innerIntegral p ∂realDensityMeasure volume (productDensityMarginal g) := hdis.2
      _ = _ := by
        rw [← hprefix]
        exact integral_map (measurable_densityPrefix j).aemeasurable hInnerMap.aestronglyMeasurable

/-- Every actual measurable normalized bounded joint density supported in
a bounded cube has a concrete conditional-density system. No
disintegration existence theorem or entropy/correlation assumption is an
input. -/
noncomputable def conditionalDensitySystem_of_bounded_cube {M : ℕ}
    (f : (Fin M → ℝ) → ℝ) (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z)
    {C R : ℝ} (hC : ∀ z, f z ≤ C) (hR : 0 ≤ R)
    (hsupport : ∀ z (j : Fin M), R < |z j| → f z = 0)
    (hnorm : (∫ z, f z) = 1) : ConditionalDensitySystem M f where
  joint_measurable := hfm
  joint_nonneg := hf
  joint_integrable := integrable_jointDensity_of_bounded_cube hfm hf hC hsupport
  joint_normalized := hnorm
  joint_log_integrable := integrable_jointDensityLog_of_bounded_cube hfm hf hC hsupport
  joint_support := ⟨R, hR, hsupport⟩
  density j p := productConditionalDensity (prefixPairDensity f j) p
  density_measurable j := productConditionalDensity_measurable (prefixPairDensity_measurable hfm j)
  density_nonneg j p := productConditionalDensity_nonneg (prefixPairDensity_nonneg hf j) p
  density_normalized j p := integral_productConditionalDensity (prefixPairDensity f j) p
  density_bounded_support j p := by
    obtain ⟨C', hC', hR'⟩ := prefixPairDensity_bounded_support hfm hf hC hsupport j
    exact productConditionalDensity_bounded_support hC' hR' p
  disintegration j q hqm hq := prefixConditionalDensity_disintegrate hfm hf
    (integrable_jointDensity_of_bounded_cube hfm hf hC hsupport) hC hsupport j q hqm hq

end Tusnady
