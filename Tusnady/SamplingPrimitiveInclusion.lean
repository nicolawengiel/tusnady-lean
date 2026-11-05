import Tusnady.SamplingTensorInclusion
import Tusnady.SamplingRefinement
import Tusnady.Shell
import Tusnady.HaarTentAffine
import Tusnady.HaarTensorPrimitive

/-! Main.pdf Lemma 5.2(a,b): actual normalized shell primitives and actual
low Haar primitives have pointwise representatives in the concrete sparse
space at cap h+3d. Membership follows from proved real affine geometry and
the actual detail expansion. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace
open DyadicFunctions

lemma psiI_mem_pointwiseSpace (a : ℕ) (i : Fin (2 ^ a)) :
    psiI a i ∈ pointwiseSpace (a + 3) := by
  apply piecewiseAffine_mem_pointwiseSpace
  refine ⟨?_, fun j => psiI_affine_on_finer a (a + 3) le_rfl i j⟩
  intro x hx
  exact psiI_zero_outside a i x (fun hi => hx (dyadicInterval_subset_unit a i hi))

theorem normalizedPrimitive_mem_sparse {d h : ℕ} (R : Witness.Shell d h) :
    Witness.normalizedPrimitive R ∈ sparsePointwiseSpace d (h + 3 * d) := by
  have hℓ : (∑ k, (R.1.depth k + 3)) ≤ h + 3 * d := by
    simp only [Finset.sum_add_distrib, R.1.sum_depth, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    omega
  have hp := tensor_pointwise_mem_sparse (H := h + 3 * d)
    (fun k => R.1.depth k + 3) hℓ (fun k => psiI (R.1.depth k) (R.2 k))
    (fun k => psiI_mem_pointwiseSpace _ _)
  exact (sparsePointwiseSpace d (h + 3 * d)).smul_mem (Witness.shellVolume h)⁻¹ hp

theorem normalizedPrimitive_sampling_coefficients {d h : ℕ} (R : Witness.Shell d h) :
    ∃ a : Fin (sparseDimension d (h + 3 * d)) → ℝ,
      ∀ x, Witness.normalizedPrimitive R x =
        ∑ i, a i * ambientBasis d (h + 3 * d) i x :=
  sparsePointwise_coefficients _ _ _ (normalizedPrimitive_mem_sparse R)

def haarPrimitiveDepth {H : ℕ} (L : Haar.Label H) : ℕ :=
  match L with
  | none => 0
  | some ⟨a, _⟩ => a.val + 1

lemma haarPrimitiveDepth_eq_level {H : ℕ} (L : Haar.Label H) :
    (haarPrimitiveDepth L : ℤ) = Haar.level L + 1 := by
  cases L with
  | none => simp [haarPrimitiveDepth, Haar.level]
  | some L => simp [haarPrimitiveDepth, Haar.level]

lemma tentI_mem_pointwiseSpace (a : ℕ) (i : Fin (2 ^ a)) :
    Haar.tentI a i ∈ pointwiseSpace (a + 1) := by
  apply piecewiseAffine_mem_pointwiseSpace
  refine ⟨?_, fun j => Haar.tentI_affine_on_finer a (a + 1) le_rfl i j⟩
  intro x hx
  exact Haar.tentI_zero_outside a i x (fun hi => hx (dyadicInterval_subset_unit a i hi))

lemma unitPatch_affine_mem_pointwiseSpace (A B : ℝ) :
    unitPatch (fun x => A * x + B) ∈ pointwiseSpace 0 := by
  apply piecewiseAffine_mem_pointwiseSpace
  refine ⟨fun x hx => by simp [unitPatch, hx], fun i => ⟨A, B, ?_⟩⟩
  intro x hx
  exact Set.indicator_of_mem (dyadicInterval_subset_unit 0 i hx) _

lemma haarPrimitive_patch_mem_pointwiseSpace {H : ℕ} (L : Haar.Label H) :
    unitPatch (Haar.primitiveValue L) ∈ pointwiseSpace (haarPrimitiveDepth L) := by
  cases L with
  | none =>
    have he : (fun x : ℝ => 1 - x) = (fun x => (-1 : ℝ) * x + 1) := by funext x; ring
    change unitPatch (fun x : ℝ => 1 - x) ∈ pointwiseSpace 0
    rw [he]
    exact unitPatch_affine_mem_pointwiseSpace (-1) 1
  | some L =>
    have he : unitPatch (Haar.primitiveValue (some L)) = -Haar.tentI L.1.val L.2 := by
      funext x
      by_cases hx : x ∈ Ico (0 : ℝ) 1
      · simp [unitPatch, Haar.primitiveValue, hx]
      · simp [unitPatch, hx,
          Haar.tentI_zero_outside _ _ x (fun hi => hx (dyadicInterval_subset_unit _ _ hi))]
    rw [he]
    exact (pointwiseSpace _).neg_mem (tentI_mem_pointwiseSpace _ _)

lemma haarNormalizedPrimitive_patch_mem_pointwiseSpace {H : ℕ} (L : Haar.Label H) :
    unitPatch (Haar.normalizedPrimitiveValue L) ∈ pointwiseSpace (haarPrimitiveDepth L) := by
  have he : unitPatch (Haar.normalizedPrimitiveValue L) =
      (Real.sqrt (Haar.mass L))⁻¹ • unitPatch (Haar.primitiveValue L) := by
    funext x
    by_cases hx : x ∈ Ico (0 : ℝ) 1 <;>
      simp [unitPatch, Haar.normalizedPrimitiveValue, hx, div_eq_mul_inv, mul_comm]
  rw [he]
  exact (pointwiseSpace _).smul_mem _ (haarPrimitive_patch_mem_pointwiseSpace L)

lemma haarPrimitiveDepth_sum {d H : ℕ} (L : Haar.TensorLabel d H) :
    ((∑ k, haarPrimitiveDepth (L k) : ℕ) : ℤ) = Haar.tensorLevel L + d := by
  simp only [Nat.cast_sum, haarPrimitiveDepth_eq_level, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Haar.tensorLevel]

theorem lowPrimitive_sampling_coefficients {d H h : ℕ} (L : Haar.TensorLabel d H)
    (hL : Haar.tensorLevel L ≤ (h : ℤ) - 1) :
    ∃ a : Fin (sparseDimension d (h + 3 * d)) → ℝ,
      ∀ x ∈ unitCube d, Haar.normalizedTensorPrimitiveValue L x =
        ∑ i, a i * ambientBasis d (h + 3 * d) i x := by
  have hℓ : ∑ k, haarPrimitiveDepth (L k) ≤ h + 3 * d := by
    have hs : (∑ k, (haarPrimitiveDepth (L k) : ℤ)) = Haar.tensorLevel L + d := by
      simpa only [Nat.cast_sum] using haarPrimitiveDepth_sum L
    have hi : ((∑ k, haarPrimitiveDepth (L k) : ℕ) : ℤ) ≤ (h + 3 * d : ℕ) := by
      push_cast
      omega
    exact_mod_cast hi
  have hp := tensor_pointwise_mem_sparse (H := h + 3 * d)
    (fun k => haarPrimitiveDepth (L k)) hℓ
    (fun k => unitPatch (Haar.normalizedPrimitiveValue (L k)))
    (fun k => haarNormalizedPrimitive_patch_mem_pointwiseSpace (L k))
  obtain ⟨a, ha⟩ := sparsePointwise_coefficients _ _ _ hp
  refine ⟨a, fun x hx => ?_⟩
  change Haar.normalizedTensorPrimitiveValue L x =
    ∑ i, a i * sparseBasis d (h + 3 * d) (sparseEnumeration d (h + 3 * d) i) x
  rw [← ha x]
  apply Finset.prod_congr rfl
  intro k _
  exact (Set.indicator_of_mem (hx k) _).symm

end Tusnady.SamplingSpace
