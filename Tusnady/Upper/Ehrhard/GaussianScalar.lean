import Tusnady.Upper.Ehrhard.GaussianIsoperimetry
import Mathlib.Probability.Independence.Basic

/-!
# Scalar Gaussian transport and planar linear marginals

The scalar measure is the actual `gaussianReal 0 1`. The interval enlargement
inequality is transported from the proved one-coordinate Euclidean theorem;
no origin assumption on the interval or closed convex set is imposed.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal InnerProductSpace Pointwise
namespace OAI.GaussianPropeller
open Quantile

/-- Unit-normal linear forms of two independent standard normals are standard. -/
theorem gaussianProduct_linear_law (c s : ℝ) (hunit : c^2+s^2=1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => c*p.1+s*p.2) = gaussianReal 0 1 := by
  let μ := (gaussianReal 0 1).prod (gaussianReal 0 1)
  have hcoord (a : ℝ) (f : ℝ × ℝ → ℝ)
      (hf : MeasurePreserving f μ (gaussianReal 0 1)) :
      μ.map (fun p => a*f p) = gaussianReal 0 (⟨a^2,sq_nonneg _⟩ : ℝ≥0) := by
    calc
      μ.map (fun p => a*f p) = (μ.map f).map (fun x : ℝ => a*x) :=
        (Measure.map_map (by fun_prop) hf.measurable).symm
      _ = _ := by rw [hf.map_eq, gaussianReal_map_const_mul]; simp [NNReal.mk]
  have h1 := hcoord c Prod.fst measurePreserving_fst
  have h2 := hcoord s Prod.snd measurePreserving_snd
  have hind : IndepFun (fun p : ℝ × ℝ => c*p.1) (fun p => s*p.2) μ :=
    indepFun_prod (by fun_prop) (by fun_prop)
  have hv : (⟨c^2,sq_nonneg _⟩ : ℝ≥0) + ⟨s^2,sq_nonneg _⟩ = 1 := by
    apply NNReal.coe_injective
    exact hunit
  have h := gaussianReal_add_gaussianReal_of_indepFun hind
    ⟨(by fun_prop : Measurable (fun p : ℝ × ℝ => c*p.1)).aemeasurable, h1⟩
    ⟨(by fun_prop : Measurable (fun p : ℝ × ℝ => s*p.2)).aemeasurable, h2⟩
  simpa only [Pi.add_apply, zero_add, hv] using! h

/-- The corresponding exact half-plane probability. -/
theorem gaussianProduct_halfspace_mass (c s : ℝ) (hunit : c^2+s^2=1) (D : ℝ) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {p : ℝ × ℝ | c*p.1+s*p.2 ≤ D} = Φ D := by
  calc
    _ = (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => c*p.1+s*p.2)).real (Iic D) := by
      simp only [measureReal_def]
      rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      rfl
    _ = Φ D := by rw [gaussianProduct_linear_law c s hunit, Φ_eq_gaussianReal]

/-- The actual one-coordinate Euclidean space is isometric to the scalar line. -/
def scalarEquiv : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ where
  toFun := fun x => x 0
  invFun := fun x => WithLp.toLp 2 (fun _ => x)
  left_inv := by intro x; ext i; have hi : i = 0 := Fin.eq_zero i; subst i; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl
  norm_map' := by
    intro x
    have hs : ‖x‖^2 = (x 0)^2 := by
      simp [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    have hn : ‖x‖ = |x 0| := by nlinarith [norm_nonneg x, abs_nonneg (x 0), sq_abs (x 0)]
    change ‖(x 0 : ℝ)‖ = ‖x‖
    simpa only [Real.norm_eq_abs] using hn.symm

lemma gaussianMeasure_scalar_law :
    (gaussianMeasure (Fin 1)).map scalarEquiv = gaussianReal 0 1 := by
  rw [gaussianMeasure, Measure.map_map scalarEquiv.continuous.measurable
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable]
  change (Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)).map (fun x => x 0) = gaussianReal 0 1
  exact (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq

/-- The scalar isometry transports probabilities of every set exactly. -/
lemma gaussianMeasure_scalar_real_preimage (I : Set ℝ) :
    (gaussianMeasure (Fin 1)).real (scalarEquiv ⁻¹' I) = (gaussianReal 0 1).real I := by
  simp only [measureReal_def]
  congr 1
  rw [← gaussianMeasure_scalar_law]
  exact (scalarEquiv.toHomeomorph.toMeasurableEquiv.map_apply I).symm

/-- Scalar closed convex Gaussian isoperimetry, including intervals away from zero. -/
theorem real_closedConvex_gaussian_isoperimetry (I : Set ℝ)
    (hIc : IsClosed I) (hIv : Convex ℝ I)
    (hIm : (gaussianReal 0 1).real I ∈ Ioo (0:ℝ) 1) {r : ℝ} (hr : 0 ≤ r) :
    Φ (q ((gaussianReal 0 1).real I)+r) ≤
      (gaussianReal 0 1).real (I + Icc (-r) r) := by
  let J : Set (EuclideanSpace ℝ (Fin 1)) := scalarEquiv ⁻¹' I
  have hJc : IsClosed J := hIc.preimage scalarEquiv.continuous
  have hJv : Convex ℝ J := hIv.linear_preimage scalarEquiv.toLinearEquiv.toLinearMap
  have hJm : (gaussianMeasure (Fin 1)).real J ∈ Ioo (0:ℝ) 1 := by
    rw [gaussianMeasure_scalar_real_preimage]
    exact hIm
  have h := closedConvex_gaussian_isoperimetry_general (by decide : 0 < 1) J hJc hJv hJm hr
  have hset : scalarEquiv ⁻¹' (I + Icc (-r) r) = J + Metric.closedBall 0 r := by
    ext z
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      refine ⟨scalarEquiv.symm a, by simpa only [J, mem_preimage, scalarEquiv.apply_symm_apply],
        scalarEquiv.symm b, ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, scalarEquiv.symm.norm_map, Real.norm_eq_abs]
        exact abs_le.mpr hb
      · apply scalarEquiv.injective
        simpa only [map_add, scalarEquiv.apply_symm_apply] using hab
    · rintro ⟨x, hx, y, hy, hxy⟩
      refine ⟨scalarEquiv x, hx, scalarEquiv y, ?_, ?_⟩
      · have hn : ‖y‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_zero_right] using hy
        have hnorm : |scalarEquiv y| = ‖y‖ := by
          simpa only [Real.norm_eq_abs] using scalarEquiv.norm_map y
        exact abs_le.mp (hnorm ▸ hn)
      · simpa only [map_add] using congrArg scalarEquiv hxy
  have hmass : (gaussianMeasure (Fin 1)).real (J + Metric.closedBall 0 r) =
      (gaussianReal 0 1).real (I + Icc (-r) r) := by
    rw [← hset]
    exact gaussianMeasure_scalar_real_preimage _
  have hmJ : (gaussianMeasure (Fin 1)).real J = (gaussianReal 0 1).real I :=
    gaussianMeasure_scalar_real_preimage I
  simpa only [hmJ, hmass] using h

end OAI.GaussianPropeller
