import Tusnady.ShellLowOrthogonality
import Tusnady.PrimitiveL2
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual shell synthesis and low-primitive orthogonality in Hilbert space

Every vector and subspace is constructed from the manuscript's real
functions. The norm identity and orthogonality are proved by the actual
integral identities, rather than supplied as Hilbert-space assumptions.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Witness
open MeasureTheory Set
open scoped BigOperators
variable {d h H : ℕ}

abbrev CubeHilbert (d : ℕ) := Lp ℝ 2 (Haar.cubeMeasure d)
abbrev ShellCoefficients (d h : ℕ) := EuclideanSpace ℝ (Shell d h)

def shellPrimitiveVector (R : Shell d h) : CubeHilbert d :=
  (normalizedPrimitive_memLp R).toLp (normalizedPrimitive R)

lemma shellPrimitiveVector_ae (R : Shell d h) :
    shellPrimitiveVector R =ᵐ[Haar.cubeMeasure d] normalizedPrimitive R :=
  (normalizedPrimitive_memLp R).coeFn_toLp

lemma shellPrimitiveVector_inner (R S : Shell d h) :
    inner ℝ (shellPrimitiveVector R) (shellPrimitiveVector S) =
      if R = S then gamma d*shellVolume h else 0 := by
  classical
  rw [L2.inner_def]
  calc
    _ = ∫ x, normalizedPrimitive R x*normalizedPrimitive S x ∂Haar.cubeMeasure d := by
      apply integral_congr_ae
      filter_upwards [shellPrimitiveVector_ae R,shellPrimitiveVector_ae S] with x hR hS
      simp only [hR,hS,RCLike.inner_apply',conj_trivial]
    _ = _ := normalizedPrimitive_orthogonality R S

def shellSynthesisLinear (d h : ℕ) : ShellCoefficients d h →ₗ[ℝ] CubeHilbert d where
  toFun x := ∑ R, x R • shellPrimitiveVector R
  map_add' x y := by simp only [PiLp.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp only [PiLp.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

def shellSynthesis (d h : ℕ) : ShellCoefficients d h →L[ℝ] CubeHilbert d :=
  (shellSynthesisLinear d h).toContinuousLinearMap

lemma shellSynthesis_ae (x : ShellCoefficients d h) :
    shellSynthesis d h x =ᵐ[Haar.cubeMeasure d] (fun p => ∑ R, x R*normalizedPrimitive R p) := by
  exact Haar.finite_sum_ae Finset.univ
    (fun R : Shell d h => x R • shellPrimitiveVector R)
    (fun R p => x R*normalizedPrimitive R p) (fun R _ => by
      filter_upwards [Lp.coeFn_smul (x R) (shellPrimitiveVector R),shellPrimitiveVector_ae R] with p hs hp
      simpa only [Pi.smul_apply,smul_eq_mul,hp] using hs)

/-- The exact manuscript shell synthesis norm, with gamma_d=192^(-d)
and shellVolume h=2^(-h), for every real Euclidean coefficient vector. -/
theorem shellSynthesis_norm_sq (x : ShellCoefficients d h) :
    ‖shellSynthesis d h x‖^2 = gamma d*shellVolume h*‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  calc
    _ = ∫ p, (∑ R, x R*normalizedPrimitive R p)^2 ∂Haar.cubeMeasure d := by
      apply integral_congr_ae
      filter_upwards [shellSynthesis_ae x] with p hp
      simp only [hp,RCLike.inner_apply',conj_trivial,sq]
    _ = gamma d*shellVolume h*∑ R, (x R)^2 := integral_sum_normalizedPrimitive_sq x
    _ = _ := by simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]

/-- The actual low primitive space K=J(low Haar cross). -/
def lowPrimitiveSpace (d H h : ℕ) : Submodule ℝ (CubeHilbert d) :=
  (Haar.lowCrossSpace d H h).map (Haar.primitiveCLM d).toLinearMap

/-- The physical representative of each low primitive basis vector is
exactly the already proved normalized tensor primitive. -/
lemma primitiveCLM_tensorL2_ae (L : Haar.TensorLabel d H) :
    Haar.primitiveCLM d (Haar.tensorL2 L) =ᵐ[Haar.cubeMeasure d] Haar.normalizedTensorPrimitiveValue L := by
  filter_upwards [Haar.primitiveCLM_ae (Haar.tensorL2 L),Haar.cubeMeasure_ae_UnitCube d] with p hJ hp
  rw [hJ,Haar.boxPrimitive_tensorL2 L p hp]

lemma shellPrimitiveVector_inner_lowTensor (R : Shell d h) (L : Haar.TensorLabel d H)
    (hL : Haar.tensorLevel L < (h:ℤ)) :
    inner ℝ (shellPrimitiveVector R) (Haar.primitiveCLM d (Haar.tensorL2 L)) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ p, normalizedPrimitive R p*Haar.normalizedTensorPrimitiveValue L p ∂Haar.cubeMeasure d := by
      apply integral_congr_ae
      filter_upwards [shellPrimitiveVector_ae R,primitiveCLM_tensorL2_ae L] with p hR hL
      simp only [hR,hL,RCLike.inner_apply',conj_trivial]
    _ = 0 := normalizedPrimitive_orthogonal_lowTensor R L hL

lemma shellPrimitiveVector_inner_low (R : Shell d h) (f : CubeHilbert d)
    (hf : f ∈ Haar.lowCrossSpace d H h) :
    inner ℝ (shellPrimitiveVector R) (Haar.primitiveCLM d f) = 0 := by
  classical
  change f ∈ Submodule.span ℝ ((Haar.lowCrossLabels d H h).image Haar.tensorL2 : Set (CubeHilbert d)) at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L,hL,rfl⟩ := Finset.mem_image.mp hf
    have hlev : Haar.tensorLevel L ≤ (h:ℤ)-1 := (Finset.mem_filter.mp hL).2
    exact shellPrimitiveVector_inner_lowTensor R L (by omega)
  | zero => simp
  | add f g _ _ hfg hgg => simp only [map_add,inner_add_right,hfg,hgg,add_zero]
  | smul c f _ hfg => simp only [map_smul,real_inner_smul_right,hfg,mul_zero]

/-- Actual low/shell orthogonality in L², with all analytic content
supplied by the proved real primitive moments. -/
theorem shellPrimitiveVector_mem_orthogonal (R : Shell d h) :
    shellPrimitiveVector R ∈ (lowPrimitiveSpace d H h)ᗮ := by
  rw [Submodule.mem_orthogonal']
  rintro _ ⟨f,hf,rfl⟩
  exact shellPrimitiveVector_inner_low R f hf

theorem shellSynthesis_mem_orthogonal (x : ShellCoefficients d h) :
    shellSynthesis d h x ∈ (lowPrimitiveSpace d H h)ᗮ := by
  apply Submodule.sum_mem
  intro R _
  exact Submodule.smul_mem _ _ (shellPrimitiveVector_mem_orthogonal R)

end Tusnady.Witness

namespace Tusnady.Witness
open MeasureTheory Set
open scoped BigOperators
variable {d h H : ℕ}

/-- The low primitive image is the span of the actual, explicitly finite
primitive basis vectors. -/
theorem lowPrimitiveSpace_eq_span (d H h : ℕ) :
    lowPrimitiveSpace d H h = Submodule.span ℝ
      ((fun L => Haar.primitiveCLM d (Haar.tensorL2 L)) ''
        (Haar.lowCrossLabels d H h : Set (Haar.TensorLabel d H))) := by
  classical
  unfold lowPrimitiveSpace Haar.lowCrossSpace Haar.spanFor
  rw [Submodule.map_span]
  simp only [Finset.coe_image,Set.image_image]
  rfl

def lowPrimitiveRepresentative (d H h : ℕ) (f : CubeHilbert d) (p : Point d) : ℝ :=
  ∑ L : Haar.lowCrossLabels d H h,
    inner ℝ (Haar.tensorL2 L.val) f * Haar.normalizedTensorPrimitiveValue L.val p

/-- Canonical finite physical representative of J applied to the low
projection. These are actual normalized tent products, not arbitrary
representatives of L² classes. -/
theorem primitive_lowProjection_ae (f : CubeHilbert d) :
    Haar.primitiveCLM d (Haar.lowProjection d H h f) =ᵐ[Haar.cubeMeasure d]
      lowPrimitiveRepresentative d H h f := by
  classical
  have hv : Haar.primitiveCLM d (Haar.lowProjection d H h f) =
      ∑ L : Haar.lowCrossLabels d H h,
        inner ℝ (Haar.tensorL2 L.val) f • Haar.primitiveCLM d (Haar.tensorL2 L.val) := by
    rw [Haar.lowProjection,Haar.projectionFor_eq_sum]
    simp only [map_sum,map_smul]
  rw [hv]
  exact Haar.finite_sum_ae Finset.univ
    (fun L : Haar.lowCrossLabels d H h =>
      inner ℝ (Haar.tensorL2 L.val) f • Haar.primitiveCLM d (Haar.tensorL2 L.val))
    (fun L p => inner ℝ (Haar.tensorL2 L.val) f*Haar.normalizedTensorPrimitiveValue L.val p)
    (fun L _ => by
      filter_upwards [Lp.coeFn_smul (inner ℝ (Haar.tensorL2 L.val) f)
        (Haar.primitiveCLM d (Haar.tensorL2 L.val)),primitiveCLM_tensorL2_ae L.val] with p hs hp
      simpa only [Pi.smul_apply,smul_eq_mul,hp] using hs)

theorem primitive_low_member_ae (f : CubeHilbert d) (hf : f ∈ Haar.lowCrossSpace d H h) :
    Haar.primitiveCLM d f =ᵐ[Haar.cubeMeasure d] lowPrimitiveRepresentative d H h f := by
  have hp : Haar.lowProjection d H h f = f :=
    (Haar.spanFor (Haar.lowCrossLabels d H h)).starProjection_eq_self_iff.mpr hf
  have ha := primitive_lowProjection_ae (d := d) (H := H) (h := h) f
  rwa [hp] at ha

end Tusnady.Witness

namespace Tusnady.Witness
open MeasureTheory
variable {d h H : ℕ}

instance lowPrimitiveSpace_finiteDimensional (d H h : ℕ) :
    FiniteDimensional ℝ (lowPrimitiveSpace d H h) := by
  unfold lowPrimitiveSpace Haar.lowCrossSpace
  infer_instance

theorem lowPrimitiveSpace_finrank_le (d H h : ℕ) :
    Module.finrank ℝ (lowPrimitiveSpace d H h) ≤ (Haar.lowCrossLabels d H h).card := by
  letI : FiniteDimensional ℝ (Haar.lowCrossSpace d H h) := by
    unfold Haar.lowCrossSpace
    infer_instance
  calc
    _ ≤ Module.finrank ℝ (Haar.lowCrossSpace d H h) :=
      Submodule.finrank_map_le _ _
    _ = _ := by
      simpa only [Haar.lowCrossSpace,Fintype.card_coe] using
        Module.finrank_eq_card_basis (Haar.basisFor (Haar.lowCrossLabels d H h)).toBasis

end Tusnady.Witness
