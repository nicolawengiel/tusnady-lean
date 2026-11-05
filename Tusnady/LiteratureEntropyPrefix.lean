import Tusnady.LiteratureEntropyIntegrability
import Tusnady.LiteratureRosenblatt
import Tusnady.EntropyDensityMarginal
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

/-! # Actual prefix densities and their factorization

All densities here are marginal integrals of the given joint density.
The factorization is derived from the recorded disintegration measure
identity, rather than postulated as additional conditional-density data.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace Tusnady.LiteratureProof
set_option maxHeartbeats 1000000

theorem measurable_takePrefix (M n : ℕ) (hn : n ≤ M) :
    Measurable (@takePrefix M n hn) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

def prefixLawN {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) : Measure (Fin n → ℝ) :=
  s.law.map (takePrefix n hn)

instance prefixLawN_probability {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) :
    IsProbabilityMeasure (prefixLawN s n hn) :=
  Measure.isProbabilityMeasure_map (measurable_takePrefix M n hn).aemeasurable

def prefixDensityN {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (_s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) (p : Fin n → ℝ) : ℝ :=
  ∫ t : DensityTail M n, f ((prefixSplit M n hn).symm (p,t))

theorem prefixDensityN_measurable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) : Measurable (prefixDensityN s n hn) :=
  integratedDensity_measurable volume (s.joint_measurable.comp (prefixSplit M n hn).symm.measurable)

theorem prefixDensityN_nonneg {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) (p : Fin n → ℝ) :
    0 ≤ prefixDensityN s n hn p := integral_nonneg (fun _ => s.joint_nonneg _)

theorem prefixDensityN_integrable {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) : Integrable (prefixDensityN s n hn) := by
  have ht : Integrable (fun p => f ((prefixSplit M n hn).symm p)) :=
    ((prefixSplit_measurePreserving M n hn).symm (prefixSplit M n hn)).integrable_comp_of_integrable
      s.joint_integrable
  exact ht.integral_prod_left

theorem prefixLawN_eq_density {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) :
    prefixLawN s n hn = realDensityMeasure volume (prefixDensityN s n hn) := by
  have ht : Integrable (fun p => f ((prefixSplit M n hn).symm p)) :=
    ((prefixSplit_measurePreserving M n hn).symm (prefixSplit M n hn)).integrable_comp_of_integrable
      s.joint_integrable
  unfold prefixLawN
  change (realDensityMeasure volume f).map (Prod.fst ∘ prefixSplit M n hn) = _
  rw [← Measure.map_map measurable_fst (prefixSplit M n hn).measurable,
    map_realDensityMeasure_equiv volume volume (prefixSplit M n hn)
      (prefixSplit_measurePreserving M n hn) f s.joint_nonneg s.joint_integrable]
  exact integratedDensity_map_fst volume volume _ (fun _ => s.joint_nonneg _) ht

theorem prefixDensityN_normalized {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) :
    (∫ p, prefixDensityN s n hn p) = 1 := by
  have hh : (∫ _ : Fin n → ℝ, (1 : ℝ) ∂prefixLawN s n hn) = 1 := by simp
  rw [prefixLawN_eq_density,
    integral_realDensityMeasure volume (prefixDensityN s n hn) (fun _ => 1)
      (prefixDensityN_measurable s n hn) (prefixDensityN_nonneg s n hn)] at hh
  simpa only [mul_one] using hh

theorem prefixDensityN_zero {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (p : Fin 0 → ℝ) :
    prefixDensityN s 0 (Nat.zero_le M) p = 1 := by
  have hconst : prefixDensityN s 0 (Nat.zero_le M) = fun _ => prefixDensityN s 0 (Nat.zero_le M) p :=
    funext (fun q => congrArg _ (Subsingleton.elim q p))
  have hh := prefixDensityN_normalized s 0 (Nat.zero_le M)
  rw [hconst] at hh
  simpa [MeasureTheory.volume_pi, Measure.pi_univ, measureReal_def] using hh

theorem prefixDensityN_full {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (z : Fin M → ℝ) : prefixDensityN s M le_rfl z = f z := by
  haveI : IsEmpty {i : Fin M // ¬i.val < M} := ⟨fun i => i.property i.val.isLt⟩
  have hh (t : DensityTail M M) : (prefixSplit M M le_rfl).symm (z,t) = z := by
    funext i
    have he := congrArg (fun w => w.1 i) ((prefixSplit M M le_rfl).apply_symm_apply (z,t))
    exact he
  simp only [prefixDensityN, hh, integral_const, smul_eq_mul]
  simp [MeasureTheory.volume_pi, measureReal_def]

theorem splitLastCoordinate_takePrefix {M : ℕ} (j : Fin M) (z : Fin M → ℝ) :
    splitLastCoordinate j.val (takePrefix (j.val+1) (Nat.succ_le_of_lt j.isLt) z) =
      (densityPrefix j z, z j) := by
  ext i
  · change takePrefix (j.val+1) (Nat.succ_le_of_lt j.isLt) z ((Fin.last j.val).succAbove i) = _
    rw [Fin.succAbove_last]
    rfl
  · rfl

theorem prefixLawN_splitLast {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    (prefixLawN s (j.val+1) (Nat.succ_le_of_lt j.isLt)).map (splitLastCoordinate j.val) =
      actualConditionalPairLaw s j := by
  rw [prefixLawN, Measure.map_map (splitLastCoordinate j.val).measurable
    (measurable_takePrefix M _ _)]
  convert actual_prefix_pair_law s j using 2
  funext z
  exact splitLastCoordinate_takePrefix j z

theorem realDensityMeasure_prod_density {X : Type*} [MeasurableSpace X]
    (base : Measure X) [SFinite base] (F : X → ℝ) (Q : X × ℝ → ℝ)
    (hF : Measurable F) (hQ : Measurable Q) (hFn : ∀ x, 0 ≤ F x) :
    realDensityMeasure ((realDensityMeasure base F).prod volume) Q =
      realDensityMeasure (base.prod volume) (fun p => F p.1 * Q p) := by
  unfold realDensityMeasure
  rw [prod_withDensity_left hF.ennreal_ofReal]
  have hmul := withDensity_mul (base.prod volume)
    (f := fun p : X × ℝ => ENNReal.ofReal (F p.1))
    (g := fun p => ENNReal.ofReal (Q p))
    (hF.ennreal_ofReal.comp measurable_fst) hQ.ennreal_ofReal
  rw [← hmul]
  congr 1
  funext p
  exact (ENNReal.ofReal_mul (hFn p.1)).symm

theorem prefixDensityN_pair_factorization {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    (fun p : (Fin j.val → ℝ) × ℝ =>
      prefixDensityN s (j.val+1) (Nat.succ_le_of_lt j.isLt) ((splitLastCoordinate j.val).symm p))
    =ᵐ[volume] (fun p => prefixDensityN s j.val j.isLt.le p.1 * s.density j p.1 p.2) := by
  have hh := prefixLawN_splitLast s j
  rw [prefixLawN_eq_density,
    map_realDensityMeasure_equiv volume volume (splitLastCoordinate j.val)
      (splitLastCoordinate_measurePreserving j.val) _ (prefixDensityN_nonneg s _ _)
      (prefixDensityN_integrable s _ _)] at hh
  have hp : actualPrefixLaw s j = realDensityMeasure volume (prefixDensityN s j.val j.isLt.le) :=
    prefixLawN_eq_density s j.val j.isLt.le
  rw [actualConditionalPairLaw, hp,
    realDensityMeasure_prod_density volume _ _ (prefixDensityN_measurable s _ _)
      (s.density_measurable j) (prefixDensityN_nonneg s _ _)] at hh
  have he := (withDensity_eq_iff_of_sigmaFinite
    ((prefixDensityN_measurable s _ _).comp (splitLastCoordinate j.val).symm.measurable).ennreal_ofReal.aemeasurable
    (((prefixDensityN_measurable s _ _).comp measurable_fst).mul
      (s.density_measurable j)).ennreal_ofReal.aemeasurable).mp hh
  filter_upwards [he] with p hp
  have hhreal := congrArg ENNReal.toReal hp
  dsimp only [Function.comp_apply] at hhreal
  simpa only [ENNReal.toReal_ofReal (prefixDensityN_nonneg s _ _ _),
    ENNReal.toReal_ofReal (mul_nonneg (prefixDensityN_nonneg s _ _ _) (s.density_nonneg j _ _))] using hhreal

/-- Marginal densities are positive at almost every observation of their own law. -/
theorem prefixDensityN_positive_ae {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) :
    ∀ᵐ z ∂s.law, 0 < prefixDensityN s n hn (takePrefix n hn z) := by
  have hp : ∀ᵐ p ∂prefixLawN s n hn, 0 < prefixDensityN s n hn p := by
    rw [prefixLawN_eq_density]
    apply (ae_withDensity_iff (prefixDensityN_measurable s n hn).ennreal_ofReal).mpr
    exact Filter.Eventually.of_forall fun p hp =>
      lt_of_not_ge (fun h => hp (ENNReal.ofReal_eq_zero.mpr h))
  exact ae_of_ae_map (measurable_takePrefix M n hn).aemeasurable hp

theorem conditionalDensity_positive_ae {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    ∀ᵐ z ∂s.law, 0 < s.density j (densityPrefix j z) (z j) := by
  have hp : ∀ᵐ p ∂actualConditionalPairLaw s j, 0 < s.density j p.1 p.2 := by
    apply (ae_withDensity_iff (s.density_measurable j).ennreal_ofReal).mpr
    exact Filter.Eventually.of_forall fun p hp =>
      lt_of_not_ge (fun h => hp (ENNReal.ofReal_eq_zero.mpr h))
  rw [← actual_prefix_pair_law] at hp
  exact ae_of_ae_map
    ((measurable_densityPrefix j).prodMk (measurable_pi_apply j)).aemeasurable hp

/-- Actual density factorization at the observed prefix and coordinate. -/
theorem prefixDensityN_step_ae {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    ∀ᵐ z ∂s.law,
      prefixDensityN s (j.val+1) (Nat.succ_le_of_lt j.isLt)
        (takePrefix (j.val+1) (Nat.succ_le_of_lt j.isLt) z) =
      prefixDensityN s j.val j.isLt.le (densityPrefix j z) *
        s.density j (densityPrefix j z) (z j) := by
  have hac : actualConditionalPairLaw s j ≪ (volume : Measure ((Fin j.val → ℝ) × ℝ)) := by
    rw [← actual_prefix_pair_law]
    change (realDensityMeasure volume f).map _ ≪ _
    rw [prefixPairDensity_map s.joint_nonneg s.joint_integrable j]
    exact withDensity_absolutelyContinuous _ _
  have hp := hac.ae_eq (prefixDensityN_pair_factorization s j)
  rw [← actual_prefix_pair_law] at hp
  have hz := ae_of_ae_map
    ((measurable_densityPrefix j).prodMk (measurable_pi_apply j)).aemeasurable hp
  filter_upwards [hz] with z hz
  have he : (splitLastCoordinate j.val).symm (densityPrefix j z,z j) =
      takePrefix (j.val+1) (Nat.succ_le_of_lt j.isLt) z := by
    rw [← splitLastCoordinate_takePrefix j z, (splitLastCoordinate j.val).symm_apply_apply]
  simpa only [he] using hz

/-- Logarithms telescope without any assumption about finite marginal entropy. -/
theorem prefixLog_step_ae {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) :
    ∀ᵐ z ∂s.law,
      Real.log (prefixDensityN s (j.val+1) (Nat.succ_le_of_lt j.isLt)
        (takePrefix (j.val+1) (Nat.succ_le_of_lt j.isLt) z)) =
      Real.log (prefixDensityN s j.val j.isLt.le (takePrefix j.val j.isLt.le z)) +
        conditionalLogDensity s j z := by
  filter_upwards [prefixDensityN_step_ae s j, prefixDensityN_positive_ae s j.val j.isLt.le,
    conditionalDensity_positive_ae s j] with z hstep hpre hcond
  change 0 < prefixDensityN s j.val j.isLt.le (densityPrefix j z) at hpre
  rw [hstep, Real.log_mul (ne_of_gt hpre) (ne_of_gt hcond)]
  rfl

end Tusnady.LiteratureProof
