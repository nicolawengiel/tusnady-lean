import Tusnady.LiteratureAnderson
import Tusnady.LiteratureGaussianUnimodal
import Tusnady.LiteratureGaussianRegression
import Mathlib.MeasureTheory.Integral.Prod

/-! Gaussian section unimodality and the elementary scalar strip correlation. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.LiteratureGaussian
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

lemma linearImage_shift_neg {k n : ℕ}
    (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ)) (K : Set (Fin n → ℝ))
    (hK : IsClosed K) (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (c : Fin n → ℝ) :
    Literature.standardGaussian k {x | A x-(-c) ∈ K} =
      Literature.standardGaussian k {x | A x-c ∈ K} := by
  classical
  by_cases hne : K.Nonempty
  · have hm (c : Fin n → ℝ) : MeasurableSet {x : Fin k → ℝ | A x-c ∈ K} :=
      hK.measurableSet.preimage (A.measurable.sub measurable_const)
    rw [gaussianConditioningMass_eq_gaussian_measure k (hm (-c)),
      gaussianConditioningMass_eq_gaussian_measure k (hm c)]
    congr 1
    exact tendsto_nhds_unique
      (integral_penalty_tendsto A K hK hne (-c))
      ((integral_penalty_tendsto A K hK hne c).congr (fun N =>
        (integral_penalty_neg N A K hsymm c).symm))
  · simp [not_nonempty_iff_eq_empty.mp hne]

/-- Full absolute-ray monotonicity for the exact matrix-defined centered
Gaussian class. The midpoint input has already been proved independently. -/
theorem centeredGaussian_section_antitone {n : ℕ} (μ : Measure (Fin n → ℝ))
    (hμ : Literature.CenteredGaussian n μ) (K : Set (Fin n → ℝ))
    (hK : IsClosed K) (hconv : Convex ℝ K) (hsymm : ∀ x, x ∈ K ↔ -x ∈ K)
    (c : Fin n → ℝ) {s t : ℝ} (hst : |s| ≤ |t|) :
    μ {x | x-t • c ∈ K} ≤ μ {x | x-s • c ∈ K} := by
  obtain ⟨k,B,rfl⟩ := hμ
  let A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) := B.mulVecLin.toContinuousLinearMap
  change ((Literature.standardGaussian k).map A) _ ≤ ((Literature.standardGaussian k).map A) _
  have hm (r : ℝ) : MeasurableSet {x : Fin n → ℝ | x-r • c ∈ K} :=
    hK.measurableSet.preimage (measurable_id.sub measurable_const)
  rw [Measure.map_apply A.measurable (hm t),Measure.map_apply A.measurable (hm s)]
  have habs (r : ℝ) :
      Literature.standardGaussian k {x | A x-r • c ∈ K} =
        Literature.standardGaussian k {x | A x-|r| • c ∈ K} := by
    by_cases hr : 0 ≤ r
    · rw [abs_of_nonneg hr]
    · rw [abs_of_neg (lt_of_not_ge hr),neg_smul]
      exact (linearImage_shift_neg A K hK hsymm (r • c)).symm
  change Literature.standardGaussian k {x | A x-t • c ∈ K} ≤
    Literature.standardGaussian k {x | A x-s • c ∈ K}
  rw [habs t,habs s]
  exact linearImage_anderson_ray_le LiteratureProof.gaussianMidpointIntegralBound
    A K hK hconv hsymm c (abs_nonneg s) hst

/-- If a bounded nonnegative scalar function is no smaller inside a
symmetric strip than at its boundary, and no larger outside, conditioning
on that strip increases its mean. The scalar measure need not be Gaussian. -/
theorem strip_integral_correlation (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (F : ℝ → ℝ) (hFm : Measurable F) (hFn : ∀ t, 0 ≤ F t)
    (hFb : ∀ t, F t ≤ 1) (c : ℝ)
    (hanti : ∀ s t : ℝ, |s| ≤ |t| → F t ≤ F s) :
    ν.real {t | |t| ≤ c}*(∫ t, F t ∂ν) ≤ ∫ t in {t | |t| ≤ c}, F t ∂ν := by
  let S : Set ℝ := {t | |t| ≤ c}
  have hS : MeasurableSet S := measurableSet_le measurable_id.abs measurable_const
  have hi : Integrable F ν := (integrable_const (1:ℝ)).mono' hFm.aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (hFn t)]; exact hFb t)
  by_cases hc : 0 ≤ c
  · have hin : ν.real S*F c ≤ ∫ t in S, F t ∂ν := by
      rw [← smul_eq_mul,← setIntegral_const]
      apply setIntegral_mono_on (integrable_const _) hi.integrableOn hS
      intro t ht
      exact hanti t c (by simpa only [abs_of_nonneg hc] using ht)
    have hout : (∫ t in Sᶜ, F t ∂ν) ≤ ν.real Sᶜ*F c := by
      rw [← smul_eq_mul,← setIntegral_const]
      apply setIntegral_mono_on hi.integrableOn (integrable_const _) hS.compl
      intro t ht
      change ¬ |t| ≤ c at ht
      exact hanti c t (by rw [abs_of_nonneg hc]; exact (lt_of_not_ge ht).le)
    have hp : 0 ≤ ν.real S := measureReal_nonneg
    have hq : 0 ≤ ν.real Sᶜ := measureReal_nonneg
    have hpq : ν.real S+ν.real Sᶜ = 1 := by
      simpa using measureReal_add_measureReal_compl (μ:=ν) hS
    have hprod := mul_le_mul_of_nonneg_left hout hp
    have hprod' := mul_le_mul_of_nonneg_left hin hq
    have hsplit := integral_add_compl hS hi
    change ν.real S*(∫ t, F t ∂ν) ≤ ∫ t in S, F t ∂ν
    have hcross : ν.real S*(∫ t in Sᶜ, F t ∂ν) ≤ ν.real Sᶜ*(∫ t in S, F t ∂ν) :=
      hprod.trans (by nlinarith only [hprod'])
    rw [← hsplit]
    calc
      _ = ν.real S*(∫ t in S, F t ∂ν)+ν.real S*(∫ t in Sᶜ, F t ∂ν) := by ring
      _ ≤ ν.real S*(∫ t in S, F t ∂ν)+ν.real Sᶜ*(∫ t in S, F t ∂ν) := add_le_add_left hcross _
      _ = _ := by rw [← add_mul,hpq,one_mul]
  · have he : S = ∅ := by
      ext t
      simp only [S,mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact not_le.mpr ((lt_of_not_ge hc).trans_le (abs_nonneg t))
    change ν.real S*(∫ t, F t ∂ν) ≤ ∫ t in S, F t ∂ν
    simp [he]

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureGaussian
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal
variable {n : ℕ}

lemma product_real_eq_integral_section (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (η : Measure (Fin n → ℝ)) [IsProbabilityMeasure η]
    (S : Set (ℝ × (Fin n → ℝ))) (hS : MeasurableSet S) :
    (ν.prod η).real S = ∫ t, η.real (Prod.mk t ⁻¹' S) ∂ν := by
  calc
    _ = ∫ p, S.indicator (fun _ => (1:ℝ)) p ∂ν.prod η := (integral_indicator_one hS).symm
    _ = ∫ t, ∫ w, S.indicator (fun _ => (1:ℝ)) (t,w) ∂η ∂ν :=
      integral_prod _ ((integrable_const (1:ℝ)).indicator hS)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      change (∫ w, (Prod.mk t ⁻¹' S).indicator 1 w ∂η) = _
      exact integral_indicator_one (hS.preimage (measurable_const.prodMk measurable_id))

/-- The product-law correlation of a scalar symmetric strip with a
section-unimodal measurable set. All probabilities refer to the actual
product measure. -/
theorem product_section_correlation (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (η : Measure (Fin n → ℝ)) [IsProbabilityMeasure η]
    (S : Set (ℝ × (Fin n → ℝ))) (hS : MeasurableSet S) (c : ℝ)
    (hanti : ∀ s t : ℝ, |s| ≤ |t| →
      η.real (Prod.mk t ⁻¹' S) ≤ η.real (Prod.mk s ⁻¹' S)) :
    ν.real {t | |t| ≤ c}*(ν.prod η).real S ≤
      (ν.prod η).real {p | |p.1| ≤ c ∧ p ∈ S} := by
  let F : ℝ → ℝ := fun t => η.real (Prod.mk t ⁻¹' S)
  have hFm : Measurable F := (measurable_measure_prodMk_left hS).ennreal_toReal
  have hcorr := strip_integral_correlation ν F hFm (fun _ => measureReal_nonneg)
    (fun _ => measureReal_le_one) c hanti
  rw [product_real_eq_integral_section ν η S hS]
  have hT : MeasurableSet {p : ℝ × (Fin n → ℝ) | |p.1| ≤ c ∧ p ∈ S} :=
    (measurableSet_le measurable_fst.abs measurable_const).inter hS
  rw [product_real_eq_integral_section ν η _ hT]
  have heq : (fun t => η.real (Prod.mk t ⁻¹' {p : ℝ × (Fin n → ℝ) | |p.1| ≤ c ∧ p ∈ S})) =
      {t : ℝ | |t| ≤ c}.indicator F := by
    funext t
    by_cases ht : |t| ≤ c
    · change η.real _ = if |t| ≤ c then F t else 0
      rw [if_pos ht]
      change η.real _ = η.real (Prod.mk t ⁻¹' S)
      congr 1
      ext w
      simp [ht]
    · change η.real _ = if |t| ≤ c then F t else 0
      rw [if_neg ht]
      have he : Prod.mk t ⁻¹' {p : ℝ × (Fin n → ℝ) | |p.1| ≤ c ∧ p ∈ S} = ∅ := by
        ext w
        simp [ht]
      simp [he]
  have hstrip : MeasurableSet {t : ℝ | |t| ≤ c} := measurableSet_le measurable_id.abs measurable_const
  rw [heq,integral_indicator hstrip]
  exact hcorr

end Tusnady.LiteratureGaussian
