import Tusnady.EntropyDensityDisintegration
import Tusnady.EntropyDensityConditional
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Explicit coordinate splittings for prefix marginal densities -/

open MeasureTheory Set
open scoped ENNReal

namespace Tusnady

def prefixIndexEquiv (M n : ℕ) (hn : n ≤ M) :
    {i : Fin M // i.val < n} ≃ Fin n where
  toFun i := ⟨i.1.val, i.2⟩
  invFun i := ⟨⟨i.val, lt_of_lt_of_le i.isLt hn⟩, i.isLt⟩
  left_inv i := by cases i; rfl
  right_inv i := rfl

abbrev DensityTail (M n : ℕ) := {i : Fin M // ¬i.val < n} → ℝ

noncomputable def prefixSplit (M n : ℕ) (hn : n ≤ M) :
    (Fin M → ℝ) ≃ᵐ (Fin n → ℝ) × DensityTail M n :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin M => ℝ) (fun i => i.val < n)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (prefixIndexEquiv M n hn))
      (MeasurableEquiv.refl _))

theorem prefixSplit_measurePreserving (M n : ℕ) (hn : n ≤ M) :
    MeasurePreserving (prefixSplit M n hn) volume volume := by
  have hid : MeasurePreserving (id : DensityTail M n → DensityTail M n) volume volume :=
    ⟨measurable_id, by simp⟩
  exact ((volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) (prefixIndexEquiv M n hn)).prod
    hid).comp (volume_preserving_piEquivPiSubtypeProd (fun _ : Fin M => ℝ)
      (fun i => i.val < n))

theorem prefixSplit_fst_apply (M n : ℕ) (hn : n ≤ M) (z : Fin M → ℝ) (i : Fin n) :
    (prefixSplit M n hn z).1 i = z ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ := by
  rfl

noncomputable def splitLastCoordinate (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).trans
    (MeasurableEquiv.prodComm)

theorem splitLastCoordinate_measurePreserving (n : ℕ) :
    MeasurePreserving (splitLastCoordinate n) volume volume := by
  exact Measure.measurePreserving_swap.comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))

noncomputable def prefixCoordinateSplit {M : ℕ} (j : Fin M) :
    (Fin M → ℝ) ≃ᵐ (((Fin j.val → ℝ) × ℝ) × DensityTail M (j.val + 1)) :=
  (prefixSplit M (j.val + 1) (Nat.succ_le_of_lt j.isLt)).trans
    (MeasurableEquiv.prodCongr (splitLastCoordinate j.val) (MeasurableEquiv.refl _))

theorem prefixCoordinateSplit_measurePreserving {M : ℕ} (j : Fin M) :
    MeasurePreserving (prefixCoordinateSplit j) volume volume := by
  have hid : MeasurePreserving
      (id : DensityTail M (j.val + 1) → DensityTail M (j.val + 1)) volume volume :=
    ⟨measurable_id, by simp⟩
  exact ((splitLastCoordinate_measurePreserving j.val).prod hid).comp
    (prefixSplit_measurePreserving M (j.val + 1) (Nat.succ_le_of_lt j.isLt))

theorem prefixCoordinateSplit_fst {M : ℕ} (j : Fin M) (z : Fin M → ℝ) :
    (prefixCoordinateSplit j z).1 = (densityPrefix j z, z j) := by
  ext i
  · change (prefixSplit M (j.val + 1) _ z).1 ((Fin.last j.val).succAbove i) = _
    rw [Fin.succAbove_last]
    rfl
  · rfl

theorem prefixCoordinateSplit_snd_apply {M : ℕ} (j : Fin M) (z : Fin M → ℝ)
    (i : {i : Fin M // ¬i.val < j.val + 1}) :
    (prefixCoordinateSplit j z).2 i = z i.1 := rfl

theorem prefixCoordinateSplit_symm_snd {M : ℕ} (j : Fin M)
    (p : (Fin j.val → ℝ) × ℝ) (t : DensityTail M (j.val + 1))
    (i : {i : Fin M // ¬i.val < j.val + 1}) :
    (prefixCoordinateSplit j).symm (p, t) i.1 = t i := by
  have h := congrArg (fun w => w.2 i) ((prefixCoordinateSplit j).apply_symm_apply (p, t))
  exact h

theorem prefixCoordinateSplit_symm_coordinate {M : ℕ} (j : Fin M)
    (p : (Fin j.val → ℝ) × ℝ) (t : DensityTail M (j.val + 1)) :
    (prefixCoordinateSplit j).symm (p, t) j = p.2 := by
  have h := congrArg (fun w => w.1.2) ((prefixCoordinateSplit j).apply_symm_apply (p, t))
  dsimp only at h
  rw [prefixCoordinateSplit_fst] at h
  exact h

/-- Change of density under an actual measure-preserving coordinate
equivalence. -/
theorem map_realDensityMeasure_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (baseX : Measure X) (baseY : Measure Y) (e : X ≃ᵐ Y)
    (he : MeasurePreserving e baseX baseY) (f : X → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f baseX) :
    (realDensityMeasure baseX f).map e = realDensityMeasure baseY (fun y => f (e.symm y)) := by
  have htrans : Integrable (fun y => f (e.symm y)) baseY :=
    (he.symm e).integrable_comp_of_integrable hfi
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply e.measurable hS,
    realDensityMeasure_apply baseX f hf hfi (e.measurable hS),
    realDensityMeasure_apply baseY (fun y => f (e.symm y)) (fun y => hf (e.symm y)) htrans hS]
  congr 1
  simpa only [e.symm_apply_apply] using
    he.setIntegral_preimage_emb e.measurableEmbedding (fun y => f (e.symm y)) S

noncomputable def integratedDensity {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (baseY : Measure Y) (g : X × Y → ℝ) (x : X) : ℝ := ∫ y, g (x, y) ∂baseY

theorem integratedDensity_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (baseY : Measure Y) [SFinite baseY] {g : X × Y → ℝ} (hgm : Measurable g) :
    Measurable (integratedDensity baseY g) :=
  hgm.stronglyMeasurable.integral_prod_right'.measurable

theorem integratedDensity_map_fst {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (baseX : Measure X) (baseY : Measure Y) [SFinite baseX] [SFinite baseY]
    (g : X × Y → ℝ) (hg : ∀ p, 0 ≤ g p) (hgi : Integrable g (baseX.prod baseY)) :
    (realDensityMeasure (baseX.prod baseY) g).map Prod.fst =
      realDensityMeasure baseX (integratedDensity baseY g) := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply measurable_fst hS]
  have hpre : Prod.fst ⁻¹' S = S ×ˢ (univ : Set Y) := by ext p; simp
  rw [hpre, realDensityMeasure_apply (baseX.prod baseY) g hg hgi (hS.prod MeasurableSet.univ),
    realDensityMeasure_apply baseX (integratedDensity baseY g)
      (fun x => integral_nonneg fun y => hg (x, y)) hgi.integral_prod_left hS]
  congr 1
  have hmeasure : (baseX.restrict S).prod baseY =
      (baseX.prod baseY).restrict (S ×ˢ (univ : Set Y)) := by
    simpa only [Measure.restrict_univ] using (Measure.prod_restrict (μ := baseX) (ν := baseY) S univ)
  have hgs : Integrable g ((baseX.restrict S).prod baseY) := by
    rw [hmeasure]
    exact hgi.integrableOn
  rw [← hmeasure, integral_prod g hgs]
  rfl

noncomputable def prefixPairDensity {M : ℕ} (f : (Fin M → ℝ) → ℝ) (j : Fin M)
    (p : (Fin j.val → ℝ) × ℝ) : ℝ :=
  ∫ t : DensityTail M (j.val + 1), f ((prefixCoordinateSplit j).symm (p, t))

theorem prefixPairDensity_measurable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (j : Fin M) : Measurable (prefixPairDensity f j) :=
  integratedDensity_measurable volume (hfm.comp (prefixCoordinateSplit j).symm.measurable)

theorem prefixPairDensity_nonneg {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hf : ∀ z, 0 ≤ f z) (j : Fin M) (p : (Fin j.val → ℝ) × ℝ) :
    0 ≤ prefixPairDensity f j p :=
  integral_nonneg fun t => hf ((prefixCoordinateSplit j).symm (p, t))

theorem prefixPairDensity_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfi : Integrable f) (j : Fin M) : Integrable (prefixPairDensity f j) := by
  have htrans : Integrable (fun p => f ((prefixCoordinateSplit j).symm p)) :=
    ((prefixCoordinateSplit_measurePreserving j).symm (prefixCoordinateSplit j)).integrable_comp_of_integrable hfi
  exact htrans.integral_prod_left

/-- The prefix/next-coordinate law has the explicit marginal density
obtained by integrating out all remaining coordinates. -/
theorem prefixPairDensity_map {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hf : ∀ z, 0 ≤ f z) (hfi : Integrable f) (j : Fin M) :
    (realDensityMeasure volume f).map (fun z => (densityPrefix j z, z j)) =
      realDensityMeasure volume (prefixPairDensity f j) := by
  have htrans : Integrable (fun p => f ((prefixCoordinateSplit j).symm p)) :=
    ((prefixCoordinateSplit_measurePreserving j).symm (prefixCoordinateSplit j)).integrable_comp_of_integrable hfi
  rw [show (fun z => (densityPrefix j z, z j)) = Prod.fst ∘ (prefixCoordinateSplit j) from
    (funext fun z => (prefixCoordinateSplit_fst j z).symm),
    ← Measure.map_map measurable_fst (prefixCoordinateSplit j).measurable,
    map_realDensityMeasure_equiv volume volume (prefixCoordinateSplit j)
      (prefixCoordinateSplit_measurePreserving j) f hf hfi]
  exact integratedDensity_map_fst volume volume (fun p => f ((prefixCoordinateSplit j).symm p))
    (fun p => hf _) htrans

theorem integratedDensity_bound_of_supported {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (baseY : Measure Y) (g : X × Y → ℝ) (hgm : Measurable g)
    (hg : ∀ p, 0 ≤ g p) {S : Set Y} (hS : MeasurableSet S) (hfinite : baseY S < ∞)
    (C : ℝ) (hC : ∀ x y, g (x, y) ≤ C) (hzero : ∀ x y, y ∉ S → g (x, y) = 0)
    (x : X) : integratedDensity baseY g x ≤ baseY.real S * C := by
  classical
  haveI : Fact (baseY S < ∞) := ⟨hfinite⟩
  have hslice : Integrable (fun y => g (x, y)) baseY := by
    apply integrable_of_bounded_supported baseY (fun y => g (x, y)) hS hfinite
      (hgm.comp (measurable_const.prodMk measurable_id)) C
    · intro y
      simpa [Real.norm_eq_abs, abs_of_nonneg (hg (x, y))] using hC x y
    · exact hzero x
  have heq : S.indicator (fun y => g (x, y)) = fun y => g (x, y) := by
    funext y
    by_cases hy : y ∈ S
    · simp [hy]
    · simp [hy, hzero x y hy]
  calc
    integratedDensity baseY g x = ∫ y in S, g (x, y) ∂baseY := by
      rw [integratedDensity, ← integral_indicator hS, heq]
    _ ≤ ∫ _ in S, C ∂baseY :=
      integral_mono hslice.integrableOn (integrable_const C) (fun y => hC x y)
    _ = baseY.real S * C := by simp [smul_eq_mul]

theorem prefixPairDensity_bounded_support {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (hfm : Measurable f) (hf : ∀ z, 0 ≤ f z) {C R : ℝ}
    (hC : ∀ z, f z ≤ C) (hR : ∀ z (i : Fin M), R < |z i| → f z = 0) (j : Fin M) :
    ∃ C' : ℝ, (∀ p y, prefixPairDensity f j (p, y) ≤ C') ∧
      (∀ p y, R < |y| → prefixPairDensity f j (p, y) = 0) := by
  classical
  let T : Set (DensityTail M (j.val + 1)) := Icc (fun _ => -R) (fun _ => R)
  let g : (((Fin j.val → ℝ) × ℝ) × DensityTail M (j.val + 1)) → ℝ :=
    fun p => f ((prefixCoordinateSplit j).symm p)
  have hgm : Measurable g := hfm.comp (prefixCoordinateSplit j).symm.measurable
  have hg : ∀ p, 0 ≤ g p := fun p => hf _
  have htail : ∀ p t, t ∉ T → g (p, t) = 0 := by
    intro p t ht
    have hnot : ¬∀ i, |t i| ≤ R := by
      intro hall
      apply ht
      exact ⟨fun i => (abs_le.mp (hall i)).1, fun i => (abs_le.mp (hall i)).2⟩
    push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    apply hR _ i.1
    rw [prefixCoordinateSplit_symm_snd]
    exact hi
  refine ⟨(volume : Measure (DensityTail M (j.val + 1))).real T * C, ?_, ?_⟩
  · intro p y
    exact integratedDensity_bound_of_supported volume g hgm hg
      (isCompact_Icc.measurableSet) isCompact_Icc.measure_lt_top C
      (fun p t => hC _) htail (p, y)
  · intro p y hy
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun t => by
      apply hR _ j
      rw [prefixCoordinateSplit_symm_coordinate]
      exact hy

end Tusnady
