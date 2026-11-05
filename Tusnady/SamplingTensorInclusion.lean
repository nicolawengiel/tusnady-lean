import Tusnady.SamplingDetailExpansion
import Tusnady.SamplingDomainBasis

/-! Actual tensor products of V_j functions lie in the concrete sparse
cross whenever the sum of their univariate levels is bounded by its cap. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

def sparsePointwiseSpace (d H : ℕ) : Submodule ℝ ((Fin d → ℝ) → ℝ) :=
  Submodule.span ℝ (Set.range (sparseBasis d H))

lemma exists_bounded_detail_coefficients (j : ℕ) (f : ℝ → ℝ) (hf : f ∈ pointwiseSpace j) :
    ∃ a : BoundedDetailIndex j → ℝ,
      ∀ x, f x = ∑ i, a i * boundedDetailBasis j i x := by
  have hm := pointwiseSpace_le_bounded j hf
  change f ∈ Submodule.span ℝ (Set.range (boundedDetailBasis j)) at hm
  rw [← Fintype.range_linearCombination] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun x => ?_⟩
  have he := congrFun ha x
  simpa [Fintype.linearCombination_apply, Finset.sum_apply] using he.symm

theorem tensor_pointwise_mem_sparse {d H : ℕ} (ℓ : Fin d → ℕ)
    (hℓ : ∑ k, ℓ k ≤ H) (f : Fin d → ℝ → ℝ)
    (hf : ∀ k, f k ∈ pointwiseSpace (ℓ k)) :
    (fun x : Fin d → ℝ => ∏ k, f k (x k)) ∈ sparsePointwiseSpace d H := by
  classical
  choose a ha using fun k => exists_bounded_detail_coefficients (ℓ k) (f k) (hf k)
  let J := ∀ k, BoundedDetailIndex (ℓ k)
  let depth : J → Fin d → ℕ := fun j k => (j k).1.val
  have hsum : ∀ j : J, ∑ k, depth j k ≤ H := fun j =>
    (Finset.sum_le_sum fun k _ => Nat.le_of_lt_succ (j k).1.isLt).trans hℓ
  let code : J → SparseIndex d H := fun j =>
    ⟨⟨(fun k => ⟨depth j k, Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun l _ => Nat.zero_le (depth j l)) (Finset.mem_univ k)).trans
        (hsum j))⟩), hsum j⟩, fun k => (j k).2⟩
  have he : (fun x : Fin d → ℝ => ∏ k, f k (x k)) =
      ∑ j : J, (∏ k, a k (j k)) • sparseBasis d H (code j) := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [ha]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.prod_mul_distrib]
    rfl
  rw [he]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨code j, rfl⟩)

theorem sparsePointwise_coefficients (d H : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : f ∈ sparsePointwiseSpace d H) :
    ∃ a : Fin (sparseDimension d H) → ℝ,
      ∀ x, f x = ∑ i, a i * sparseBasis d H (sparseEnumeration d H i) x := by
  classical
  change f ∈ Submodule.span ℝ (Set.range (sparseBasis d H)) at hf
  rw [← Fintype.range_linearCombination] at hf
  obtain ⟨b, hb⟩ := hf
  refine ⟨fun i => b (sparseEnumeration d H i), fun x => ?_⟩
  have he := congrFun hb x
  simp only [Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [← (sparseEnumeration d H).sum_comp (fun i => b i * sparseBasis d H i x)] at he
  exact he.symm

end Tusnady.SamplingSpace
