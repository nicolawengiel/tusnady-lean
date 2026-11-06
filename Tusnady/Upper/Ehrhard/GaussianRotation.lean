import Tusnady.Upper.Ehrhard.GaussianBase
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Actual Gaussian linear marginals and orthogonal invariance

These statements concern the explicit product Gaussian from `GaussianBase`.
The characteristic function is derived from finite sums of independent real
Gaussians; orthogonal invariance follows from its radial formula.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace
namespace OAI.GaussianPropeller

lemma productGaussian_sum_law {ι : Type*} [Fintype ι] (a : ι → ℝ) (S : Finset ι) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (fun z => ∑ j ∈ S, a j * z j) =
      gaussianReal 0 (∑ j ∈ S, (⟨a j ^ 2, sq_nonneg (a j)⟩ : ℝ≥0)) := by
  classical
  let P := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have hmeas : ∀ j : ι, Measurable (fun z : ι → ℝ => a j * z j) := by
    intro j
    fun_prop
  have hind : iIndepFun (fun j : ι => fun z : ι → ℝ => a j * z j) P := by
    exact iIndepFun_pi (fun j => (measurable_const.mul measurable_id).aemeasurable)
  have hcoord : ∀ j : ι, P.map (fun z => a j * z j) =
      gaussianReal 0 (⟨a j ^ 2, sq_nonneg (a j)⟩ : ℝ≥0) := by
    intro j
    have heval : P.map (fun z : ι → ℝ => z j) = gaussianReal 0 1 := by
      exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) j).map_eq
    calc
      P.map (fun z => a j * z j) =
          (P.map (fun z : ι → ℝ => z j)).map (fun x => a j * x) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
      _ = gaussianReal 0 (⟨a j ^ 2, sq_nonneg (a j)⟩ : ℝ≥0) := by
        rw [heval, gaussianReal_map_const_mul]
        simp [NNReal.mk]
  induction S using Finset.induction_on with
  | empty => simp [gaussianReal_zero_var]
  | @insert j S hj ih =>
    have hpair := (hind.indepFun_finsetSum_of_notMem hmeas hj).symm
    have hfun : (∑ l ∈ S, fun z : ι → ℝ => a l * z l) =
        (fun z : ι → ℝ => ∑ l ∈ S, a l * z l) := by
      funext z
      simp only [Finset.sum_apply]
    have hsum : P.map (∑ l ∈ S, fun z : ι → ℝ => a l * z l) =
        gaussianReal 0 (∑ l ∈ S, (⟨a l ^ 2, sq_nonneg (a l)⟩ : ℝ≥0)) := by
      simpa only [hfun] using ih
    have h := gaussianReal_add_gaussianReal_of_indepFun hpair
      ⟨(hmeas j).aemeasurable, hcoord j⟩
      ⟨by
        rw [hfun]
        exact (Finset.measurable_sum S (fun l _ => hmeas l)).aemeasurable, hsum⟩
    have hadd : ((fun z : ι → ℝ => a j * z j) +
        ∑ l ∈ S, fun z : ι → ℝ => a l * z l) =
        (fun z => ∑ l ∈ insert j S, a l * z l) := by
      funext z
      simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_insert hj]
    rw [hadd] at h
    simpa only [Finset.sum_insert hj, zero_add] using h

/-- The exact one-dimensional law, including the zero-vector degeneracy. -/
theorem gaussianMeasure_inner_law {ι : Type*} [Fintype ι] (u : EuclideanSpace ℝ ι) :
    (gaussianMeasure ι).map (fun x => inner ℝ u x) =
      gaussianReal 0 (‖u‖^2).toNNReal := by
  classical
  have hv : (∑ i : ι, (⟨(u i)^2, sq_nonneg _⟩ : ℝ≥0)) = (‖u‖^2).toNNReal := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [NNReal.coe_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact NNReal.coe_mk _ _
  unfold gaussianMeasure
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  convert productGaussian_sum_law (fun i => u i) Finset.univ using 1
  · congr 1
    funext z
    simp only [Function.comp_def, PiLp.inner_apply, RCLike.inner_apply', conj_trivial,
      PiLp.toLp_apply]
  · exact congrArg (gaussianReal 0) hv.symm

lemma gaussianMeasure_charFun {ι : Type*} [Fintype ι] (t : EuclideanSpace ℝ ι) :
    charFun (gaussianMeasure ι) t = Complex.exp (-((‖t‖^2 : ℝ) : ℂ) / 2) := by
  have heq : charFun (gaussianMeasure ι) t =
      charFun ((gaussianMeasure ι).map (fun x => inner ℝ t x)) 1 := by
    rw [charFun_apply, charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [real_inner_comm t x, RCLike.inner_apply, conj_trivial, one_mul]
  rw [heq, gaussianMeasure_inner_law, charFun_gaussianReal]
  norm_num [Real.coe_toNNReal _ (sq_nonneg _)]
  congr 1
  ring

/-- Every linear isometry equivalence preserves the actual standard Gaussian. -/
theorem gaussianMeasure_map_linearIsometryEquiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ) :
    (gaussianMeasure ι).map e = gaussianMeasure κ := by
  apply Measure.ext_of_charFun
  funext t
  have heq : charFun ((gaussianMeasure ι).map e) t =
      charFun (gaussianMeasure ι) (e.symm t) := by
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop), charFun_apply]
    apply integral_congr_ae
    filter_upwards [] with x
    congr 1
    congr 1
    exact congrArg (fun r : ℝ => (r : ℂ))
      (by simpa only [e.apply_symm_apply] using (e.inner_map_map x (e.symm t)))
  rw [heq, gaussianMeasure_charFun, gaussianMeasure_charFun, e.symm.norm_map]

/-- Every affine hyperplane with a nonzero normal has zero Gaussian measure. -/
theorem gaussianMeasure_hyperplane_null {ι : Type*} [Fintype ι]
    (u : EuclideanSpace ℝ ι) (hu : u ≠ 0) (a : ℝ) :
    gaussianMeasure ι {x | inner ℝ u x = a} = 0 := by
  have hv : (‖u‖^2).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hu)))
  letI : NullSingletonClass (gaussianReal 0 (‖u‖^2).toNNReal) :=
    nullSingletonClass_gaussianReal hv
  have h := congrArg (fun μ : Measure ℝ => μ {a}) (gaussianMeasure_inner_law u)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton a), measure_singleton] at h
  exact h

end OAI.GaussianPropeller
