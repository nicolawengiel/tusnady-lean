import Tusnady.LiteratureRosenblattScalar

/-! # Rosenblatt uniformity from the actual disintegration system -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace Tusnady.LiteratureProof
attribute [local instance] Classical.propDecidable

def extendPrefix {M : ℕ} (n : ℕ) (p : Fin n → ℝ) : Fin M → ℝ :=
  fun i => if hi : i.val < n then p ⟨i.val, hi⟩ else 0

theorem measurable_extendPrefix (M n : ℕ) : Measurable (@extendPrefix M n) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i.val < n <;> simp only [extendPrefix, hi, ↓reduceDIte]
  · exact measurable_pi_apply _
  · exact measurable_const

def takePrefix {M : ℕ} (n : ℕ) (hn : n ≤ M) (z : Fin M → ℝ) : Fin n → ℝ :=
  fun i => z ⟨i.val, lt_of_lt_of_le i.isLt hn⟩

def prefixTransform {M : ℕ} {f : (Fin M → ℝ) → ℝ} (s : ConditionalDensitySystem M f)
    (n : ℕ) (hn : n ≤ M) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  s.cdfTransform (extendPrefix n p) ⟨i.val, lt_of_lt_of_le i.isLt hn⟩

theorem measurable_prefixTransform {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) :
    Measurable (prefixTransform s n hn) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).comp (s.measurable_cdfTransform.comp (measurable_extendPrefix M n))

theorem prefixTransform_takePrefix {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) (z : Fin M → ℝ) (i : Fin n) :
    prefixTransform s n hn (takePrefix n hn z) i =
      s.cdfTransform z ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ := by
  let j : Fin M := ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  have hpref : densityPrefix j (extendPrefix n (takePrefix n hn z)) = densityPrefix j z := by
    funext k
    have hk : k.val < n := k.isLt.trans i.isLt
    simp only [densityPrefix, extendPrefix, takePrefix, hk, ↓reduceDIte]
  have hcoord : extendPrefix n (takePrefix n hn z) j = z j := by
    simp only [extendPrefix, takePrefix, j, i.isLt, ↓reduceDIte]
  change 2 * cdf (realDensityMeasure volume (s.density j
    (densityPrefix j (extendPrefix n (takePrefix n hn z)))))
      (extendPrefix n (takePrefix n hn z) j) - 1 = _
  rw [hpref, hcoord]
  rfl

def indicatorOne (E : Set ℝ) (x : ℝ) : ℝ := E.indicator (fun _ => (1 : ℝ)) x

theorem indicatorOne_abs_le (E : Set ℝ) (x : ℝ) : |indicatorOne E x| ≤ 1 := by
  by_cases hx : x ∈ E <;> simp [indicatorOne, hx]

def prefixProduct {M : ℕ} {f : (Fin M → ℝ) → ℝ} (s : ConditionalDensitySystem M f)
    (n : ℕ) (hn : n ≤ M) (E : Fin M → Set ℝ) (z : Fin M → ℝ) : ℝ :=
  ∏ i : Fin n, indicatorOne (E ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)
    (s.cdfTransform z ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)

def prefixTest {M : ℕ} {f : (Fin M → ℝ) → ℝ} (s : ConditionalDensitySystem M f)
    (n : ℕ) (hn : n ≤ M) (E : Fin M → Set ℝ) (p : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, indicatorOne (E ⟨i.val, lt_of_lt_of_le i.isLt hn⟩)
    (prefixTransform s n hn p i)

theorem measurable_prefixTest {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M)
    (E : Fin M → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) : Measurable (prefixTest s n hn E) := by
  apply Finset.measurable_prod
  intro i _
  exact ((measurable_const.indicator (hE _))).comp
    ((measurable_pi_apply i).comp (measurable_prefixTransform s n hn))

theorem prefixTest_abs_le {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M)
    (E : Fin M → Set ℝ) (p : Fin n → ℝ) : |prefixTest s n hn E p| ≤ 1 := by
  rw [prefixTest, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) (fun _ _ => indicatorOne_abs_le _ _)

theorem prefixTest_takePrefix {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M)
    (E : Fin M → Set ℝ) (z : Fin M → ℝ) :
    prefixTest s n hn E (takePrefix n hn z) = prefixProduct s n hn E z := by
  unfold prefixTest prefixProduct
  simp_rw [prefixTransform_takePrefix]

theorem scalar_conditional_cdf_map {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (p : Fin j.val → ℝ) :
    (realDensityMeasure volume (s.density j p)).map
      (fun y => 2 * cdf (realDensityMeasure volume (s.density j p)) y - 1) =
        UniformMonomial.scalarLaw := by
  let μ := realDensityMeasure volume (s.density j p)
  letI : IsProbabilityMeasure μ := isProbabilityMeasure_realDensityMeasure volume (s.density j p)
    ((s.density_measurable j).comp (measurable_const.prodMk measurable_id))
    (s.density_nonneg j p) (s.scalar_integrable j p) (s.density_normalized j p)
  letI : NullSingletonClass μ := by unfold μ realDensityMeasure; infer_instance
  exact normalized_cdf_map_uniform μ

theorem scalar_conditional_indicator_integral {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (p : Fin j.val → ℝ)
    (E : Set ℝ) (hE : MeasurableSet E) :
    (∫ y, indicatorOne E (2 * cdf (realDensityMeasure volume (s.density j p)) y - 1)
      ∂realDensityMeasure volume (s.density j p)) = UniformMonomial.scalarLaw.real E := by
  have hF : Measurable (fun y => 2 * cdf (realDensityMeasure volume (s.density j p)) y - 1) :=
    ((monotone_cdf _).measurable.const_mul 2).sub_const 1
  unfold indicatorOne
  rw [← integral_map hF.aemeasurable (measurable_const.indicator hE).aestronglyMeasurable,
    scalar_conditional_cdf_map]
  exact integral_indicator_one hE

def disintegrationTest {M : ℕ} {f : (Fin M → ℝ) → ℝ} (s : ConditionalDensitySystem M f)
    (j : Fin M) (E : Fin M → Set ℝ) (p : (Fin j.val → ℝ) × ℝ) : ℝ :=
  prefixTest s j.val (Nat.le_of_lt j.isLt) E p.1 * indicatorOne (E j)
    (2 * cdf (realDensityMeasure volume (s.density j p.1)) p.2 - 1)

theorem measurable_disintegrationTest {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (E : Fin M → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) : Measurable (disintegrationTest s j E) := by
  have hCDF := measurable_cdf_realDensityMeasure_family (s.density j)
    (s.density_measurable j) (s.density_nonneg j) (s.scalar_integrable j) (s.density_normalized j)
  exact ((measurable_prefixTest s j.val (Nat.le_of_lt j.isLt) E hE).comp measurable_fst).mul
    ((measurable_const.indicator (hE j)).comp ((hCDF.const_mul 2).sub_const 1))

theorem disintegrationTest_abs_le {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (E : Fin M → Set ℝ)
    (p : (Fin j.val → ℝ) × ℝ) : |disintegrationTest s j E p| ≤ 1 := by
  rw [disintegrationTest, abs_mul]
  exact (mul_le_mul (prefixTest_abs_le s j.val _ E p.1) (indicatorOne_abs_le _ _)
    (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem disintegrationTest_joint {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (E : Fin M → Set ℝ) (z : Fin M → ℝ) :
    disintegrationTest s j E (densityPrefix j z, z j) =
      prefixProduct s j.val (Nat.le_of_lt j.isLt) E z * indicatorOne (E j) (s.cdfTransform z j) := by
  unfold disintegrationTest
  rw [show densityPrefix j z = takePrefix j.val (Nat.le_of_lt j.isLt) z from rfl,
    prefixTest_takePrefix]
  rfl

theorem disintegrationTest_integral {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (E : Fin M → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) (p : Fin j.val → ℝ) :
    (∫ y, disintegrationTest s j E (p, y) ∂realDensityMeasure volume (s.density j p)) =
      prefixTest s j.val (Nat.le_of_lt j.isLt) E p * UniformMonomial.scalarLaw.real (E j) := by
  change (∫ y, prefixTest s j.val _ E p * indicatorOne (E j)
    (2 * cdf (realDensityMeasure volume (s.density j p)) y - 1)
      ∂realDensityMeasure volume (s.density j p)) = _
  rw [integral_const_mul, scalar_conditional_indicator_integral s j p (E j) (hE j)]

theorem prefixProduct_step_integral {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (j : Fin M) (E : Fin M → Set ℝ)
    (hE : ∀ i, MeasurableSet (E i)) :
    (∫ z, prefixProduct s j.val (Nat.le_of_lt j.isLt) E z *
      indicatorOne (E j) (s.cdfTransform z j) ∂s.law) =
        (∫ z, prefixProduct s j.val (Nat.le_of_lt j.isLt) E z ∂s.law) *
          UniformMonomial.scalarLaw.real (E j) := by
  have hqm := measurable_disintegrationTest s j E hE
  have hqi : Integrable (fun z => disintegrationTest s j E (densityPrefix j z, z j)) s.law := by
    apply Integrable.of_bound
      (hqm.comp ((measurable_densityPrefix j).prodMk (measurable_pi_apply j))).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun z => disintegrationTest_abs_le s j E _
  have heq := (s.disintegration j (disintegrationTest s j E) hqm hqi).2
  simp_rw [disintegrationTest_joint, disintegrationTest_integral s j E hE,
    show densityPrefix j = takePrefix j.val (Nat.le_of_lt j.isLt) from rfl,
    prefixTest_takePrefix] at heq
  rwa [integral_mul_const] at heq

theorem prefixProduct_integral {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M)
    (E : Fin M → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) :
    (∫ z, prefixProduct s n hn E z ∂s.law) =
      ∏ i : Fin n, UniformMonomial.scalarLaw.real (E ⟨i.val, lt_of_lt_of_le i.isLt hn⟩) := by
  induction n with
  | zero => simp [prefixProduct]
  | succ k ih =>
    have hk : k ≤ M := Nat.le_trans (Nat.le_succ k) hn
    let j : Fin M := ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hn⟩
    have hprod (z : Fin M → ℝ) : prefixProduct s (k + 1) hn E z =
        prefixProduct s k hk E z * indicatorOne (E j) (s.cdfTransform z j) := by
      unfold prefixProduct
      rw [Fin.prod_univ_castSucc]
      rfl
    simp_rw [hprod]
    rw [prefixProduct_step_integral s j E hE, ih hk, Fin.prod_univ_castSucc]
    rfl

theorem indicator_product {α : Type*} [Fintype α] (E : α → Set ℝ) (u : α → ℝ) :
    (∏ i : α, indicatorOne (E i) (u i)) = (Set.pi univ E).indicator (fun _ => (1 : ℝ)) u := by
  by_cases hu : u ∈ Set.pi univ E
  · rw [Set.indicator_of_mem hu]
    apply Finset.prod_eq_one
    intro i _
    have hi : u i ∈ E i := hu i (mem_univ i)
    simp only [indicatorOne, Set.indicator_of_mem hi]
  · rw [Set.indicator_of_notMem hu]
    obtain ⟨i, hi⟩ : ∃ i : α, u i ∉ E i := by
      simpa only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] using hu
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [indicatorOne, Set.indicator_of_notMem hi]

/-- The classical Rosenblatt theorem for exactly the general actual
conditional-density system in Literature.lean. The proof uses every
prefix disintegration identity and the proved scalar transform theorem. -/
theorem rosenblattUniform : Literature.RosenblattUniform := by
  intro M f s
  apply Eq.symm
  apply Measure.pi_eq
  intro E hE
  rw [Measure.map_apply s.measurable_cdfTransform (MeasurableSet.univ_pi hE)]
  let A := s.cdfTransform ⁻¹' Set.pi univ E
  have hA : MeasurableSet A := (MeasurableSet.univ_pi hE).preimage s.measurable_cdfTransform
  have hprod (z : Fin M → ℝ) : prefixProduct s M le_rfl E z = A.indicator (fun _ => (1 : ℝ)) z := by
    change (∏ i : Fin M, indicatorOne (E i) (s.cdfTransform z i)) = _
    have hi := indicator_product E (s.cdfTransform z)
    simpa only [A, Set.indicator_apply, Set.mem_preimage] using hi
  have hint : (∫ z, prefixProduct s M le_rfl E z ∂s.law) = s.law.real A := by
    simp_rw [hprod]
    exact integral_indicator_one hA
  have hreal := (prefixProduct_integral s M le_rfl E hE).symm.trans hint
  have hmeasure : s.law A = ENNReal.ofReal (s.law.real A) := by
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top s.law A)]
  change s.law A = _
  rw [hmeasure, ← hreal]
  simp only [measureReal_def]
  rw [← ENNReal.toReal_prod]
  apply ENNReal.ofReal_toReal
  exact (ENNReal.prod_lt_top (fun i _ => measure_lt_top UniformMonomial.scalarLaw (E i))).ne

end Tusnady.LiteratureProof
