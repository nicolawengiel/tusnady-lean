import Tusnady.Upper.Ehrhard.GaussianSections
import Tusnady.Upper.Ehrhard.ConeTranslation

/-!
# Euclidean plane coordinates and the actual Gaussian product

The coordinate chart from the Euclidean plane to `ℝ × ℝ` is a continuous
linear equivalence. It preserves the actual Gaussian law. Its product target
has the usual product norm, so this chart is not asserted to be an isometry.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal
namespace OAI.GaussianPropeller.GaussianPlane
open Quantile

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The actual coordinate chart, with no assertion about the product norm. -/
def planeProductEquiv : Plane ≃L[ℝ] (ℝ × ℝ) where
  toFun := fun z => (z 0, z 1)
  invFun := fun p => WithLp.toLp 2 ![p.1, p.2]
  left_inv := by intro z; ext i; fin_cases i <;> rfl
  right_inv := by intro p; cases p; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl
  continuous_toFun :=
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).prodMk
      (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1)
  continuous_invFun := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd

@[simp] lemma planeProductEquiv_fst (z : Plane) : (planeProductEquiv z).1 = z 0 := rfl
@[simp] lemma planeProductEquiv_snd (z : Plane) : (planeProductEquiv z).2 = z 1 := rfl
@[simp] lemma planeProductEquiv_symm_zero (p : ℝ × ℝ) :
    planeProductEquiv.symm p 0 = p.1 := rfl
@[simp] lemma planeProductEquiv_symm_one (p : ℝ × ℝ) :
    planeProductEquiv.symm p 1 = p.2 := rfl

/-- The coordinate chart sends the actual Euclidean Gaussian to the product
of two actual standard real Gaussian measures. -/
theorem planeProduct_law :
    (gaussianMeasure (Fin 2)).map planeProductEquiv = HalfplaneFold.gaussianProduct := by
  have hscalar : MeasurePreserving scalarEquiv (gaussianMeasure (Fin 1))
      (gaussianReal 0 1) := ⟨scalarEquiv.continuous.measurable, gaussianMeasure_scalar_law⟩
  have h := ((hscalar.prod (MeasurePreserving.id (gaussianReal 0 1))).comp
    (GaussianSections.split_measurePreserving (k := 1))).map_eq
  have hfun : (planeProductEquiv : Plane → ℝ × ℝ) =
      Prod.map (scalarEquiv : EuclideanSpace ℝ (Fin 1) → ℝ) id ∘ GaussianSections.split := by
    funext z
    rfl
  rw [hfun]
  exact h

/-- Exact transport for arbitrary sets, using the measurable equivalence. -/
theorem planeProduct_real_preimage (S : Set (ℝ × ℝ)) :
    (gaussianMeasure (Fin 2)).real (planeProductEquiv ⁻¹' S) =
      HalfplaneFold.gaussianProduct.real S := by
  simp only [measureReal_def]
  congr 1
  rw [← planeProduct_law]
  exact (planeProductEquiv.toHomeomorph.toMeasurableEquiv.map_apply S).symm

/-- Exact image transport, again for every set. -/
theorem planeProduct_real_image (K : Set Plane) :
    HalfplaneFold.gaussianProduct.real (planeProductEquiv '' K) =
      (gaussianMeasure (Fin 2)).real K := by
  rw [← planeProduct_real_preimage]
  congr 1
  exact preimage_image_eq K planeProductEquiv.injective

/-- A unit-normal half-plane has the exact normal CDF probability. -/
theorem halfspace_mass (c s : ℝ) (hunit : c^2+s^2=1) (D : ℝ) :
    (gaussianMeasure (Fin 2)).real {z : Plane | c*z 0+s*z 1 ≤ D} = Φ D := by
  calc
    _ = HalfplaneFold.gaussianProduct.real {p : ℝ × ℝ | c*p.1+s*p.2 ≤ D} :=
      planeProduct_real_preimage _
    _ = _ := gaussianProduct_halfspace_mass c s hunit D

/-- The proved small-radius half-plane fold estimate in Euclidean coordinates. -/
theorem halfplane_fold_mass_of_small_radius (c s d r : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (hd : 0 ≤ d) (hr : 0 < r) (hsmall : r ≤ (1 : ℝ)/1000) :
    let w := -q ((gaussianReal 0 1).real (Icc (-r) r))
    Φ d ≤ (gaussianMeasure (Fin 2)).real
      {z : Plane | z 0 ≤ (d+s*w)/c ∧ c*z 0+s*z 1 ≤ d+r*s} := by
  dsimp only
  have h := HalfplaneFold.halfplane_fold_mass_of_small_radius c s d r hc hs hunit hd hr hsmall
  change Φ d ≤ (gaussianMeasure (Fin 2)).real
    (planeProductEquiv ⁻¹' {p : ℝ × ℝ |
      p.1 ≤ (d+s*(-q ((gaussianReal 0 1).real (Icc (-r) r))))/c ∧
      c*p.1+s*p.2 ≤ d+r*s})
  rw [planeProduct_real_preimage]
  exact h

/-- The supporting-cone translation estimate in Euclidean coordinates. -/
theorem supporting_cone_mass_le (c s D d r w : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hd : 0 ≤ d) (hDd : d ≤ D) (hw : 0 ≤ w) :
    (gaussianMeasure (Fin 2)).real
      {z : Plane | (D+s*w)/c < z 0 ∧ c*z 0+s*z 1 ≤ D+r*s} ≤
    (gaussianMeasure (Fin 2)).real
      {z : Plane | (d+s*w)/c < z 0 ∧ c*z 0+s*z 1 ≤ d+r*s} := by
  change (gaussianMeasure (Fin 2)).real
      (planeProductEquiv ⁻¹' HalfplaneFold.cone c s (D+r*s) ((D+s*w)/c)) ≤
    (gaussianMeasure (Fin 2)).real
      (planeProductEquiv ⁻¹' HalfplaneFold.cone c s (d+r*s) ((d+s*w)/c))
  rw [planeProduct_real_preimage, planeProduct_real_preimage]
  exact ConeTranslation.supporting_cone_mass_le c s D d r w hc hs hd hDd hw

end OAI.GaussianPropeller.GaussianPlane
