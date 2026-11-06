import Tusnady.LiteratureGaussianSections

/-! Šidák's centered Gaussian rectangle inequality from actual Gaussian
regression and the proved section monotonicity. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.LiteratureGaussian
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal
variable {k n : ℕ}

/-- A zero-variance Gaussian scalar is genuinely independent of every
other linear image, including degenerate ones. -/
lemma gaussian_indep_of_variance_zero (μ : Measure (Fin k → ℝ)) [IsGaussian μ]
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (hvar : Var[X; μ] = 0) : IndepFun X Y μ := by
  have hX : MemLp X 2 μ := IsGaussian.memLp_dual μ X 2 (by norm_num)
  have he : eVar[X; μ] = 0 := by rw [← ofReal_variance hX,hvar]; simp
  have hae := (evariance_eq_zero_iff X.measurable.aemeasurable).1 he
  exact (indepFun_const_left (∫ z, X z ∂μ) Y).congr hae.symm (EventuallyEq.rfl)

/-- Strip correlation for a genuine centered Gaussian law and arbitrary
linear images. The proof constructs the residual, proves its independence,
and applies Fubini to its actual product law. No regression or conditional
section inequality is supplied as a premise. -/
theorem centeredGaussian_strip_correlation (μ : Measure (Fin k → ℝ))
    (hμ : Literature.CenteredGaussian k μ)
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (c : ℝ) :
    μ.real {z | |X z| ≤ c}*μ.real {z | Y z ∈ K} ≤
      μ.real {z | |X z| ≤ c ∧ Y z ∈ K} := by
  letI := centeredGaussian_isGaussian k μ hμ
  have hmstrip : MeasurableSet {t : ℝ | |t| ≤ c} :=
    measurableSet_le continuous_abs.measurable measurable_const
  by_cases hvar : Var[X; μ] = 0
  · have hind := gaussian_indep_of_variance_zero μ X Y hvar
    have he := hind.measure_inter_preimage_eq_mul {t : ℝ | |t| ≤ c} K hmstrip hK.measurableSet
    have her := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_mul,measureReal_def,Set.preimage_setOf_eq, Set.preimage, Set.inter_def, Set.mem_setOf_eq] using her.symm.le
  · let Z := regressionResidual μ X Y
    let β := regressionCoefficient μ X Y
    let ν := μ.map X
    let η := μ.map Z
    let S : Set (ℝ × (Fin n → ℝ)) := {p | p.2+p.1 • β ∈ K}
    have hSm : MeasurableSet S :=
      hK.measurableSet.preimage (measurable_snd.add (measurable_fst.smul measurable_const))
    have hTm : MeasurableSet {p : ℝ × (Fin n → ℝ) | |p.1| ≤ c ∧ p ∈ S} :=
      (measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter hSm
    have hη : Literature.CenteredGaussian n η :=
      GaussianCover.centeredGaussian_linear_image μ hμ Z.toLinearMap
    have hind := regressionResidual_indep μ X Y hvar
    have hlaw : μ.map (fun z => (X z,Z z)) = ν.prod η :=
      (indepFun_iff_map_prod_eq_prod_map_map X.measurable.aemeasurable Z.measurable.aemeasurable).1 hind
    have hrecover (z : Fin k → ℝ) : Z z+X z • β = Y z := by
      ext j
      simp only [Z,β,regressionResidual_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      ring
    have hanti : ∀ s t : ℝ, |s| ≤ |t| →
        η.real (Prod.mk t ⁻¹' S) ≤ η.real (Prod.mk s ⁻¹' S) := by
      intro s t hst
      have h := centeredGaussian_section_antitone η hη K hK hconv hsymm (-β) hst
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      simpa only [S,Set.preimage_setOf_eq,smul_neg,sub_neg_eq_add] using h
    have hc := product_section_correlation ν η S hSm c hanti
    have hfirst : ν.real {t | |t| ≤ c} = μ.real {z | |X z| ≤ c} := by
      dsimp only [ν,measureReal_def]
      rw [Measure.map_apply X.measurable hmstrip]
      rfl
    have hrest : (ν.prod η).real S = μ.real {z | Y z ∈ K} := by
      have heq : (fun z => (X z,Z z)) ⁻¹' S = {z | Y z ∈ K} := by
        ext z
        change Z z+X z • β ∈ K ↔ Y z ∈ K
        rw [hrecover]
      rw [← hlaw,measureReal_def,Measure.map_apply (X.measurable.prodMk Z.measurable) hSm,heq]
      rfl
    have hfull : (ν.prod η).real {p : ℝ × (Fin n → ℝ) | |p.1| ≤ c ∧ p ∈ S} =
        μ.real {z | |X z| ≤ c ∧ Y z ∈ K} := by
      have heq : (fun z => (X z,Z z)) ⁻¹' {p : ℝ × (Fin n → ℝ) | |p.1| ≤ c ∧ p ∈ S} =
          {z | |X z| ≤ c ∧ Y z ∈ K} := by
        ext z
        change (|X z| ≤ c ∧ Z z+X z • β ∈ K) ↔ (|X z| ≤ c ∧ Y z ∈ K)
        rw [hrecover]
      rw [← hlaw,measureReal_def,Measure.map_apply (X.measurable.prodMk Z.measurable) hTm,heq]
      rfl
    rwa [hfirst,hrest,hfull] at hc

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureGaussian
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal
variable {k : ℕ}

/-- The rectangle inequality for any finite family of actual linear
observables of a centered Gaussian source, stated first in real
probabilities. Repeated, zero and dependent observables are included. -/
theorem sidak_real_linear (μ : Measure (Fin k → ℝ))
    (hμ : Literature.CenteredGaussian k μ) (m : ℕ)
    (L : Fin m → StrongDual ℝ (Fin k → ℝ)) (c : Fin m → ℝ) :
    (∏ i, μ.real {z | |L i z| ≤ c i}) ≤ μ.real {z | ∀ i, |L i z| ≤ c i} := by
  classical
  letI := centeredGaussian_isGaussian k μ hμ
  induction m with
  | zero => simp
  | succ m ih =>
    let X := L 0
    let Y : (Fin k → ℝ) →L[ℝ] (Fin m → ℝ) := ContinuousLinearMap.pi (fun j => L j.succ)
    let K : Set (Fin m → ℝ) := {y | ∀ j, |y j| ≤ c j.succ}
    have hK : IsClosed K := by
      change IsClosed {y : Fin m → ℝ | ∀ j, |y j| ≤ c j.succ}
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun j => isClosed_le (continuous_apply j).abs continuous_const
    have hKpi : K = Set.pi Set.univ (fun j => Icc (-c j.succ) (c j.succ)) := by
      ext y
      change (∀ j, |y j| ≤ c j.succ) ↔ ∀ j ∈ Set.univ, y j ∈ Icc (-c j.succ) (c j.succ)
      simp only [Set.mem_univ,forall_const,Set.mem_Icc,abs_le]
    have hconv : Convex ℝ K := by
      rw [hKpi]
      exact convex_pi (fun _ _ => convex_Icc _ _)
    have hsymm : ∀ y, y ∈ K ↔ -y ∈ K := by
      intro y
      simp only [K,Set.mem_setOf_eq,Pi.neg_apply,abs_neg]
    have hcorr := centeredGaussian_strip_correlation μ hμ X Y K hK hconv hsymm (c 0)
    change μ.real {z | |L 0 z| ≤ c 0}*μ.real {z | ∀ j : Fin m, |L j.succ z| ≤ c j.succ} ≤
      μ.real {z | |L 0 z| ≤ c 0 ∧ ∀ j : Fin m, |L j.succ z| ≤ c j.succ} at hcorr
    calc
      _ = μ.real {z | |L 0 z| ≤ c 0} *
          ∏ j : Fin m, μ.real {z | |L j.succ z| ≤ c j.succ} := Fin.prod_univ_succ _
      _ ≤ μ.real {z | |L 0 z| ≤ c 0} *
          μ.real {z | ∀ j : Fin m, |L j.succ z| ≤ c j.succ} :=
        mul_le_mul_of_nonneg_left (ih (fun j => L j.succ) (fun j => c j.succ)) measureReal_nonneg
      _ ≤ _ := by simpa only [Fin.forall_fin_succ] using hcorr

/-- Exactly the declared Šidák input, proved for every matrix-defined
centered Gaussian law, with singular and zero covariance allowed. -/
theorem sidak : Literature.Sidak := by
  intro n μ hμ c _hc
  letI := centeredGaussian_isGaussian n μ hμ
  have h := sidak_real_linear μ hμ n (fun i => ContinuousLinearMap.proj i) c
  apply (ENNReal.toReal_le_toReal (ENNReal.prod_ne_top (fun _ _ => measure_ne_top _ _)) (by finiteness)).1
  simpa only [ENNReal.toReal_prod,measureReal_def,ContinuousLinearMap.proj_apply] using h

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureProof
/-- The second exact Gaussian literature premise is now discharged. -/
theorem sidak : Literature.Sidak := LiteratureGaussian.sidak
end Tusnady.LiteratureProof
