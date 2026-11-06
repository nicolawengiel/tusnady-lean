import Tusnady.HaarL2

/-! # Concrete representatives and bounds for the actual low/high projections. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open scoped BigOperators

lemma finite_sum_ae {d : ℕ} {α : Type*} (s : Finset α)
    (v : α → Lp ℝ 2 (cubeMeasure d)) (F : α → (Fin d → ℝ) → ℝ)
    (hv : ∀ a ∈ s, v a =ᵐ[cubeMeasure d] F a) :
    ((∑ a ∈ s, v a) : Lp ℝ 2 (cubeMeasure d)) =ᵐ[cubeMeasure d] (fun x => ∑ a ∈ s, F a x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero ℝ 2 (cubeMeasure d)] with x hx
    simpa only [Finset.sum_empty, Pi.zero_apply] using hx
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hrest := ih (fun b hb => hv b (Finset.mem_insert_of_mem hb))
    filter_upwards [Lp.coeFn_add (v a) (∑ b ∈ s, v b), hv a (Finset.mem_insert_self _ _), hrest]
      with x hAdd hA hRest
    rw [Finset.sum_insert ha]
    exact hAdd.trans (congrArg₂ (·+·) hA hRest)

lemma projectionFor_eq_finsetSum {d H : ℕ} (s : Finset (TensorLabel d H))
    (f : Lp ℝ 2 (cubeMeasure d)) :
    projectionFor s f = ∑ l ∈ s, inner ℝ (tensorL2 l) f • tensorL2 l := by
  rw [projectionFor_eq_sum]
  exact Finset.sum_coe_sort s (fun l => inner ℝ (tensorL2 l) f • tensorL2 l)

/-- The finite real function representing the actual orthogonal projection. -/
def projectionRepresentative {d H : ℕ} (s : Finset (TensorLabel d H))
    (f : Lp ℝ 2 (cubeMeasure d)) (x : Fin d → ℝ) : ℝ :=
  ∑ l ∈ s, inner ℝ (tensorL2 l) f * normalizedTensorValue l x

/-- The finite real representative agrees almost everywhere with the actual
mathlib L² orthogonal projection. -/
theorem projectionFor_ae_representative {d H : ℕ} (s : Finset (TensorLabel d H))
    (f : Lp ℝ 2 (cubeMeasure d)) :
    projectionFor s f =ᵐ[cubeMeasure d] projectionRepresentative s f := by
  rw [projectionFor_eq_finsetSum]
  unfold projectionRepresentative
  apply finite_sum_ae s (fun l => inner ℝ (tensorL2 l) f • tensorL2 l)
    (fun l x => inner ℝ (tensorL2 l) f * normalizedTensorValue l x)
  intro l _
  filter_upwards [Lp.coeFn_smul (inner ℝ (tensorL2 l) f) (tensorL2 l), tensorL2_ae l]
    with x hsmul hb
  exact hsmul.trans (congrArg (fun y => inner ℝ (tensorL2 l) f*y) hb)

/-- Real representative of the high projection, with the exact finite
subtraction of the low Haar cross. -/
theorem highProjection_ae_representative {d H : ℕ} (h : ℕ)
    (f : Lp ℝ 2 (cubeMeasure d)) :
    highProjection d H h f =ᵐ[cubeMeasure d]
      (fun x => f x-projectionRepresentative (lowCrossLabels d H h) f x) := by
  filter_upwards [Lp.coeFn_sub f (lowProjection d H h f),
    projectionFor_ae_representative (lowCrossLabels d H h) f] with x hsub hp
  exact hsub.trans (congrArg (fun y => f x-y) hp)

/-- Contractivity of the actual finite orthogonal projection. -/
theorem projectionFor_norm_le {d H : ℕ} (s : Finset (TensorLabel d H))
    (f : Lp ℝ 2 (cubeMeasure d)) : ‖projectionFor s f‖ ≤ ‖f‖ :=
  (spanFor s).norm_orthogonalProjection_apply_le f

/-- The high projection is also contractive, as the projection to the
orthogonal complement, rather than merely a difference of bounded maps. -/
theorem highProjection_norm_le {d H : ℕ} (h : ℕ)
    (f : Lp ℝ 2 (cubeMeasure d)) : ‖highProjection d H h f‖ ≤ ‖f‖ := by
  let s := lowCrossLabels d H h
  change ‖f-(spanFor s).starProjection f‖ ≤ ‖f‖
  rw [← (spanFor s).starProjection_orthogonal_val]
  exact (spanFor s)ᗮ.norm_starProjection_apply_le f

/-- Idempotence is inherited from the actual orthogonal projection. -/
theorem projectionFor_idempotent {d H : ℕ} (s : Finset (TensorLabel d H))
    (f : Lp ℝ 2 (cubeMeasure d)) :
    projectionFor s (projectionFor s f) = projectionFor s f := by
  exact congrArg (fun v : spanFor s => (v : Lp ℝ 2 (cubeMeasure d)))
    ((spanFor s).orthogonalProjection_mem_subspace_eq_self ((spanFor s).orthogonalProjection f))

end Tusnady.Haar
