import Tusnady.HaarTensor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual L² tensor Haar vectors and finite low-cross projections

The vectors below are the `toLp` classes of the concrete real tensor Haar
functions. Their orthonormality is derived from the proved real integrals.
The low-cross operator is mathlib's actual orthogonal projection onto the
explicit finite span, not a hypothesized projection interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators NNReal ENNReal

@[measurability, fun_prop]
theorem indicatorI_measurable (a : ℕ) (i : Fin (2^a)) : Measurable (indicatorI a i) := by
  unfold indicatorI dyadicInterval
  exact measurable_const.indicator measurableSet_Ico

@[measurability, fun_prop]
theorem hI_measurable (a : ℕ) (i : Fin (2^a)) : Measurable (hI a i) :=
  (indicatorI_measurable _ _).sub (indicatorI_measurable _ _)

@[measurability, fun_prop]
theorem value_measurable {H : ℕ} (label : Label H) : Measurable (value label) := by
  cases label with
  | none => exact measurable_const
  | some label => exact hI_measurable label.1.val label.2

@[measurability, fun_prop]
theorem normalizedValue_measurable {H : ℕ} (label : Label H) : Measurable (normalizedValue label) :=
  (value_measurable label).div_const _

@[measurability, fun_prop]
theorem normalizedTensorValue_measurable {d H : ℕ} (label : TensorLabel d H) :
    Measurable (normalizedTensorValue label) := by
  exact Finset.measurable_prod Finset.univ
    (fun k _ => (normalizedValue_measurable (label k)).comp (measurable_pi_apply k))

/-- Square integrability follows from the proved actual diagonal integral 1.
No integrability or orthogonality assumption about the constructed tensor
family is introduced. -/
theorem normalizedTensorValue_memLp {d H : ℕ} (label : TensorLabel d H) :
    MemLp (normalizedTensorValue label) 2 (cubeMeasure d) := by
  have hdiag : (∫ x, normalizedTensorValue label x^2 ∂cubeMeasure d) = 1 := by
    simpa only [pow_two, if_pos rfl, ite_true] using integral_normalizedTensorValue_mul label label
  have hint : Integrable (fun x => normalizedTensorValue label x^2) (cubeMeasure d) := by
    by_contra h
    rw [integral_undef h] at hdiag
    norm_num at hdiag
  exact (memLp_two_iff_integrable_sq
    (normalizedTensorValue_measurable label).aestronglyMeasurable).2 hint

/-- The actual L² equivalence class of the concrete normalized tensor. -/
def tensorL2 {d H : ℕ} (label : TensorLabel d H) : Lp ℝ 2 (cubeMeasure d) :=
  (normalizedTensorValue_memLp label).toLp (normalizedTensorValue label)

lemma tensorL2_ae {d H : ℕ} (label : TensorLabel d H) :
    tensorL2 label =ᵐ[cubeMeasure d] normalizedTensorValue label :=
  (normalizedTensorValue_memLp label).coeFn_toLp

/-- Exact Hilbert-space inner products, checked against the real representatives. -/
theorem tensorL2_inner {d H : ℕ} (L K : TensorLabel d H) :
    inner ℝ (tensorL2 L) (tensorL2 K) = if L = K then 1 else 0 := by
  classical
  rw [L2.inner_def]
  calc
    (∫ x, inner ℝ (tensorL2 L x) (tensorL2 K x) ∂cubeMeasure d) =
        ∫ x, normalizedTensorValue L x*normalizedTensorValue K x ∂cubeMeasure d := by
      apply integral_congr_ae
      filter_upwards [tensorL2_ae L, tensorL2_ae K] with x hx hy
      rw [hx, hy]
      simp only [RCLike.inner_apply', conj_trivial]
    _ = _ := integral_normalizedTensorValue_mul L K

/-- An actual orthonormal family in mathlib's Hilbert space L². -/
theorem tensorL2_orthonormal (d H : ℕ) :
    Orthonormal ℝ (tensorL2 (d := d) (H := H)) := by
  classical
  exact orthonormal_iff_ite.mpr tensorL2_inner

/-- The span of a specified finite set of actual tensor Haar vectors. -/
def spanFor {d H : ℕ} (s : Finset (TensorLabel d H)) :
    Submodule ℝ (Lp ℝ 2 (cubeMeasure d)) := by
  classical
  exact Submodule.span ℝ (s.image tensorL2 : Set (Lp ℝ 2 (cubeMeasure d)))

instance spanFor_finiteDimensional {d H : ℕ} (s : Finset (TensorLabel d H)) :
    FiniteDimensional ℝ (spanFor s) := by
  classical
  exact FiniteDimensional.span_of_finite ℝ (Finset.finite_toSet (s.image tensorL2))

instance spanFor_complete {d H : ℕ} (s : Finset (TensorLabel d H)) : CompleteSpace (spanFor s) :=
  FiniteDimensional.complete ℝ (spanFor s)

/-- The actual orthonormal basis of this finite span. -/
def basisFor {d H : ℕ} (s : Finset (TensorLabel d H)) :
    OrthonormalBasis s ℝ (spanFor s) := by
  classical
  exact OrthonormalBasis.span (tensorL2_orthonormal d H) s

@[simp] lemma basisFor_coe {d H : ℕ} (s : Finset (TensorLabel d H)) (l : s) :
    ((basisFor s) l : Lp ℝ 2 (cubeMeasure d)) = tensorL2 l.val := by
  classical
  exact OrthonormalBasis.span_apply (tensorL2_orthonormal d H) s l

/-- Orthogonal projection, returned as an ambient L² vector. -/
def projectionFor {d H : ℕ} (s : Finset (TensorLabel d H))
    (f : Lp ℝ 2 (cubeMeasure d)) : Lp ℝ 2 (cubeMeasure d) :=
  (spanFor s).orthogonalProjection f

/-- The projection is the finite coefficient sum with the actual tensor vectors. -/
theorem projectionFor_eq_sum {d H : ℕ} (s : Finset (TensorLabel d H))
    (f : Lp ℝ 2 (cubeMeasure d)) :
    projectionFor s f = ∑ l : s, inner ℝ (tensorL2 l.val) f • tensorL2 l.val := by
  classical
  have h := (basisFor s).orthogonalProjectionOnto_apply_eq_sum f
  have h' := congrArg (fun v : spanFor s => (v : Lp ℝ 2 (cubeMeasure d))) h
  simpa only [projectionFor, Submodule.coe_sum, Submodule.coe_smul,
    basisFor_coe] using h'

/-- A Haar coordinate is either retained exactly or removed exactly. -/
theorem projectionFor_tensorL2 {d H : ℕ} (s : Finset (TensorLabel d H))
    (K : TensorLabel d H) :
    projectionFor s (tensorL2 K) = if K ∈ s then tensorL2 K else 0 := by
  classical
  rw [projectionFor_eq_sum]
  by_cases hk : K ∈ s
  · rw [if_pos hk]
    let k : s := ⟨K,hk⟩
    rw [Finset.sum_eq_single k]
    · simp only [k, tensorL2_inner, ite_true, one_smul]
    · intro l _ hlk
      have hne : l.val ≠ K := by intro h; apply hlk; exact Subtype.ext h
      rw [tensorL2_inner, if_neg hne, zero_smul]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ k))
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro l _
    have hne : l.val ≠ K := by intro h; apply hk; rw [← h]; exact l.property
    rw [tensorL2_inner, if_neg hne, zero_smul]

/-- Concrete finite low Haar cross. -/
def lowCrossSpace (d H h : ℕ) : Submodule ℝ (Lp ℝ 2 (cubeMeasure d)) :=
  spanFor (lowCrossLabels d H h)

/-- Concrete actual low projection. -/
def lowProjection (d H h : ℕ) (f : Lp ℝ 2 (cubeMeasure d)) : Lp ℝ 2 (cubeMeasure d) :=
  projectionFor (lowCrossLabels d H h) f

/-- High projection is the complementary actual orthogonal projection. -/
def highProjection (d H h : ℕ) (f : Lp ℝ 2 (cubeMeasure d)) : Lp ℝ 2 (cubeMeasure d) :=
  f-lowProjection d H h f

/-- Exact low-level retention criterion, with the constant level -1. -/
theorem lowProjection_tensorL2 {d H : ℕ} (h : ℕ) (K : TensorLabel d H) :
    lowProjection d H h (tensorL2 K) =
      if tensorLevel K ≤ (h:ℤ)-1 then tensorL2 K else 0 := by
  rw [lowProjection, projectionFor_tensorL2]
  simp only [lowCrossLabels, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The high projection retains precisely levels at least h. -/
theorem highProjection_tensorL2 {d H : ℕ} (h : ℕ) (K : TensorLabel d H) :
    highProjection d H h (tensorL2 K) =
      if (h:ℤ) ≤ tensorLevel K then tensorL2 K else 0 := by
  unfold highProjection
  rw [lowProjection_tensorL2]
  by_cases hlo : tensorLevel K ≤ (h:ℤ)-1
  · rw [if_pos hlo, if_neg (by omega)]
    simp
  · rw [if_neg hlo, if_pos (by omega)]
    simp

end Tusnady.Haar
