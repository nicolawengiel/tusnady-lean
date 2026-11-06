import Tusnady.Upper.Ehrhard.SmoothedConcavity
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Linear changes of the Gaussian smoothing kernel

This extends the proved smooth quantile-concavity theorem to invertible
linear kernels, using the actual adjoint and transformed derivative bounds.
Degenerate kernels will subsequently be obtained by a dominated limit.
This is used by the completed fold proof in `VerticalFoldMonotonicity`.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace NNReal
namespace OAI.GaussianPropeller.EhrhardSmooth
open Quantile HeatConvolution
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- Gaussian quantile of smoothing in the directions of the linear map A. -/
def quantileLinearHeat (f : E → ℝ) (A : E →L[ℝ] E) (x : E) : ℝ :=
  q (∫ z, Φ (f (x + A z)) ∂gaussianMeasure ι)

set_option backward.isDefEq.respectTransparency false in
theorem quantileLinearHeat_concave_equiv
    {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hK : Continuous K)
    {L : ℝ≥0} {D : ℝ} (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D)
    (hconc : ConcaveOn ℝ univ f) (e : E ≃L[ℝ] E) :
    ConcaveOn ℝ univ (quantileLinearHeat f e.toContinuousLinearMap) := by
  let A := e.toContinuousLinearMap
  let B := ContinuousLinearMap.adjoint A
  let f' : E → ℝ := f ∘ e
  let g' : E → E := fun x => B (g (e x))
  let K' : E → E →L[ℝ] E := fun x => B.comp ((K (e x)).comp A)
  have hf' (x : E) : HasFDerivAt f' (innerSL ℝ (g' x)) x := by
    convert (hf (e x)).comp x e.hasFDerivAt using 1
    ext y
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, g']
    exact ContinuousLinearMap.adjoint_inner_left A y (g (e x))
  have hg' (x : E) : HasFDerivAt g' (K' x) x := by
    exact B.hasFDerivAt.comp x ((hg (e x)).comp x e.hasFDerivAt)
  have hK' : Continuous K' := by
    dsimp [K']
    fun_prop
  let L' : ℝ≥0 := ‖B‖₊ * L
  have hL' (x : E) : ‖g' x‖ ≤ L' := by
    exact (B.le_opNorm (g (e x))).trans
      (mul_le_mul_of_nonneg_left (hL (e x)) (norm_nonneg B))
  have hD' (x : E) : ‖K' x‖ ≤ ‖B‖ * (D * ‖A‖) := by
    calc
      _ ≤ ‖B‖ * ‖(K (e x)).comp A‖ := B.opNorm_comp_le _
      _ ≤ ‖B‖ * (‖K (e x)‖ * ‖A‖) :=
        mul_le_mul_of_nonneg_left ((K (e x)).opNorm_comp_le A) (norm_nonneg B)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hD (e x)) (norm_nonneg A)) (norm_nonneg B)
  have hconc' : ConcaveOn ℝ univ f' := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    change a * f (e x) + b * f (e y) ≤ f (e (a • x + b • y))
    rw [map_add, map_smul, map_smul]
    exact hconc.2 (mem_univ _) (mem_univ _) ha hb hab
  have hh := qheat_concave hf' hg' hK' hL' hD' hconc' (T := 1) (by norm_num)
  have hh' : ConcaveOn ℝ univ ((qheat f' 1) ∘ e.symm) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    change a * qheat f' 1 (e.symm x) + b * qheat f' 1 (e.symm y) ≤
      qheat f' 1 (e.symm (a • x + b • y))
    rw [map_add, map_smul, map_smul]
    exact hh.2 (mem_univ _) (mem_univ _) ha hb hab
  have heq : quantileLinearHeat f A = (qheat f' 1) ∘ e.symm := by
    funext x
    simp only [quantileLinearHeat, qheat, heat, f', Function.comp_def, Real.sqrt_one,
      one_smul, map_add, e.apply_symm_apply]
    rfl
  exact heq ▸ hh'

/-- A pointwise limit of invertible noise kernels also preserves the smooth
quantile concavity.  The integrals use domination by one, so singular limiting
covariances create no boundary or density assumptions. -/
theorem quantileLinearHeat_concave_of_equiv_approx
    {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hK : Continuous K)
    {L : ℝ≥0} {D : ℝ} (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D)
    (hconc : ConcaveOn ℝ univ f) (A : E →L[ℝ] E)
    (e : ℕ → E ≃L[ℝ] E) (he : ∀ z, Tendsto (fun n => e n z) atTop (𝓝 (A z))) :
    ConcaveOn ℝ univ (quantileLinearHeat f A) := by
  have hcf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hf x).continuousAt)
  have hlimit (x : E) :
      Tendsto (fun n => quantileLinearHeat f (e n).toContinuousLinearMap x) atTop
        (𝓝 (quantileLinearHeat f A x)) := by
    have hint := tendsto_integral_of_dominated_convergence (μ := gaussianMeasure ι)
      (bound := fun _ : E => (1 : ℝ))
      (F := fun n z => Φ (f (x + e n z))) (f := fun z => Φ (f (x + A z)))
      (fun n => (continuous_Φ.comp (hcf.comp (continuous_const.add (e n).continuous))).aestronglyMeasurable)
      (integrable_const _) (fun n => ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]
        exact (Φ_lt_one _).le))
      (ae_of_all _ (fun z => (continuous_Φ.continuousAt.tendsto.comp
        (hcf.continuousAt.tendsto.comp (tendsto_const_nhds.add (he z))))))
    have hmem : (∫ z, Φ (f (x + A z)) ∂gaussianMeasure ι) ∈ Ioo (0 : ℝ) 1 :=
      integral_Φ_mem (hcf.comp (continuous_const.add A.continuous)).aestronglyMeasurable
    exact (continuousAt_q hmem).tendsto.comp hint
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  exact le_of_tendsto_of_tendsto
    ((hlimit x).const_smul a |>.add ((hlimit y).const_smul b)) (hlimit (a • x + b • y))
    (Filter.Eventually.of_forall fun n =>
      (quantileLinearHeat_concave_equiv hf hg hK hL hD hconc (e n)).2
        (mem_univ x) (mem_univ y) ha hb hab)

end OAI.GaussianPropeller.EhrhardSmooth
