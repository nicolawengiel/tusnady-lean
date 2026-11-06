import Tusnady.GaussianMarginals
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Independence.CharacteristicFunction

/-! Actual Gaussian linear-image and regression infrastructure. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.LiteratureGaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

lemma linearForm_eq_sum {k : ℕ} (L : StrongDual ℝ (Fin k → ℝ)) (z : Fin k → ℝ) :
    L z = ∑ i, L (Pi.single i 1)*z i := by
  classical
  have hz : z = ∑ i, z i • (Pi.single i (1:ℝ) : Fin k → ℝ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  calc
    _ = L (∑ i, z i • (Pi.single i (1:ℝ) : Fin k → ℝ)) := congrArg L hz
    _ = _ := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul]
      simp only [smul_eq_mul]
      ring

/-- The project's matrix Gaussian definition is connected to mathlib's
actual all-linear-marginals Gaussian class. -/
instance standardGaussian_isGaussian (k : ℕ) : IsGaussian (Literature.standardGaussian k) := by
  constructor
  intro L
  let v : ℝ≥0 := ∑ i : Fin k, (⟨L (Pi.single i 1)^2,sq_nonneg _⟩ : ℝ≥0)
  have hmap : (Literature.standardGaussian k).map L = gaussianReal 0 v := by
    have h := GaussianMarginals.standardGaussian_sum_law (fun i => L (Pi.single i 1)) Finset.univ
    simpa only [← linearForm_eq_sum] using h
  have hmean : (∫ z, L z ∂Literature.standardGaussian k) = 0 := by
    have hi := integral_map (μ := Literature.standardGaussian k) L.measurable.aemeasurable
      (measurable_id : Measurable (id : ℝ → ℝ)).aestronglyMeasurable
    rw [hmap] at hi
    simpa only [id_eq,integral_id_gaussianReal] using hi.symm
  have hvar : Var[L; Literature.standardGaussian k] = (v:ℝ) := by
    rw [← variance_id_map L.measurable.aemeasurable,hmap,variance_id_gaussianReal]
  rw [hmap,hmean,hvar,Real.toNNReal_coe]

lemma centeredGaussian_isGaussian (n : ℕ) (μ : Measure (Fin n → ℝ))
    (hμ : Literature.CenteredGaussian n μ) : IsGaussian μ := by
  obtain ⟨k,B,rfl⟩ := hμ
  let A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) := B.mulVecLin.toContinuousLinearMap
  change IsGaussian ((Literature.standardGaussian k).map A)
  infer_instance

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureGaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {k n : ℕ}

/-- Gaussian uncorrelatedness implies genuine independence, proved by
characteristic functions for the actual joint law. No Gaussian
independence theorem is assumed. -/
theorem gaussian_indep_of_covariance_zero (μ : Measure (Fin k → ℝ)) [IsGaussian μ]
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (hcov : ∀ L : StrongDual ℝ (Fin n → ℝ), cov[X, L.comp Y; μ] = 0) : IndepFun X Y μ := by
  apply (indepFun_iff_charFunDual_prod X.measurable.aemeasurable Y.measurable.aemeasurable).2
  intro L
  let L₁ : StrongDual ℝ ℝ := L.comp (.inl ℝ ℝ (Fin n → ℝ))
  let L₂ : StrongDual ℝ (Fin n → ℝ) := L.comp (.inr ℝ ℝ (Fin n → ℝ))
  let Z := X.prod Y
  have hsplit : L.comp Z = L₁.comp X+L₂.comp Y := by
    ext z
    change L (X z,Y z) = L (X z,0)+L (0,Y z)
    rw [← map_add]
    simp
  have hL₁ (r : ℝ) : L₁ r = L₁ 1*r := by
    have hh := L₁.map_smul r (1:ℝ)
    simpa only [smul_eq_mul,mul_one,mul_comm] using hh
  have hfirst : (L₁.comp X : (Fin k → ℝ) → ℝ) = fun z => L₁ 1*X z := by
    funext z
    exact hL₁ (X z)
  have hz : cov[L₁.comp X,L₂.comp Y; μ] = 0 := by
    rw [hfirst,covariance_const_mul_left,hcov,mul_zero]
  have hX : MemLp (L₁.comp X) 2 μ := IsGaussian.memLp_dual μ _ 2 (by norm_num)
  have hY : MemLp (L₂.comp Y) 2 μ := IsGaussian.memLp_dual μ _ 2 (by norm_num)
  change charFunDual (μ.map Z) L = _
  rw [charFunDual_map,charFunDual_map,charFunDual_map,hsplit,
    IsGaussian.charFunDual_eq,IsGaussian.charFunDual_eq,IsGaussian.charFunDual_eq,
    ← Complex.exp_add]
  congr 1
  simp_rw [integral_complex_ofReal]
  have hm : (∫ z, (L₁.comp X+L₂.comp Y) z ∂μ) =
      (∫ z, L₁.comp X z ∂μ)+(∫ z, L₂.comp Y z ∂μ) :=
    integral_add (MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) hX)
      (MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) hY)
  have hv : Var[⇑(L₁.comp X+L₂.comp Y); μ] =
      Var[L₁.comp X; μ]+2*cov[L₁.comp X,L₂.comp Y; μ]+Var[L₂.comp Y; μ] := variance_add hX hY
  rw [hm,hv,hz]
  dsimp only [L₁,L₂]
  push_cast
  ring

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureGaussian
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
variable {k n : ℕ}

lemma gaussian_indep_of_coordinate_covariance_zero (μ : Measure (Fin k → ℝ)) [IsGaussian μ]
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (hcov : ∀ j : Fin n, cov[X, fun z => Y z j; μ] = 0) : IndepFun X Y μ := by
  apply gaussian_indep_of_covariance_zero μ X Y
  intro L
  have hf : (L.comp Y : (Fin k → ℝ) → ℝ) =
      fun z => ∑ j, L (Pi.single j 1)*Y z j := by
    funext z
    exact linearForm_eq_sum L (Y z)
  have hY : ∀ j : Fin n, MemLp (fun z => Y z j) 2 μ := fun j =>
    IsGaussian.memLp_dual μ ((ContinuousLinearMap.proj j).comp Y) 2 (by norm_num)
  rw [hf,covariance_fun_sum_right (fun j => (hY j).const_mul (L (Pi.single j 1)))
    (IsGaussian.memLp_dual μ X 2 (by norm_num))]
  simp_rw [covariance_const_mul_right,hcov,mul_zero]
  simp

def regressionCoefficient (μ : Measure (Fin k → ℝ))
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ)) : Fin n → ℝ :=
  fun j => cov[X, fun z => Y z j; μ]/Var[X; μ]

def regressionResidual (μ : Measure (Fin k → ℝ))
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) := Y-X.smulRight (regressionCoefficient μ X Y)

@[simp] lemma regressionResidual_apply (μ : Measure (Fin k → ℝ))
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ)) (z : Fin k → ℝ) (j : Fin n) :
    regressionResidual μ X Y z j = Y z j-regressionCoefficient μ X Y j*X z := by
  simp [regressionResidual,smul_eq_mul,mul_comm]

/-- The residual is actually uncorrelated with the regressed coordinate,
by the literal covariance/variance coefficient; no regression premise. -/
lemma regressionResidual_covariance_zero (μ : Measure (Fin k → ℝ)) [IsGaussian μ]
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (hvar : Var[X; μ] ≠ 0) (j : Fin n) :
    cov[X,fun z => regressionResidual μ X Y z j; μ] = 0 := by
  have hX : MemLp X 2 μ := IsGaussian.memLp_dual μ X 2 (by norm_num)
  have hY : MemLp (fun z => Y z j) 2 μ :=
    IsGaussian.memLp_dual μ ((ContinuousLinearMap.proj j).comp Y) 2 (by norm_num)
  simp_rw [regressionResidual_apply]
  change cov[X,(fun z => Y z j)-(fun z => regressionCoefficient μ X Y j*X z); μ] = 0
  rw [covariance_sub_right hX hY (hX.const_mul (regressionCoefficient μ X Y j)),
    covariance_const_mul_right,covariance_self X.measurable.aemeasurable,regressionCoefficient]
  field_simp
  ring

/-- Genuine Gaussian regression independence, including singular residual
covariance and with no inversion of a multivariate covariance matrix. -/
theorem regressionResidual_indep (μ : Measure (Fin k → ℝ)) [IsGaussian μ]
    (X : (Fin k → ℝ) →L[ℝ] ℝ) (Y : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (hvar : Var[X; μ] ≠ 0) : IndepFun X (regressionResidual μ X Y) μ :=
  gaussian_indep_of_coordinate_covariance_zero μ X _ (regressionResidual_covariance_zero μ X Y hvar)

end Tusnady.LiteratureGaussian
