import Tusnady.Upper.OrthantPrefixGeometry

/-!
# From a projected factorization and prefix bounds to original orthants

This is a proved algebraic reduction.  Its prefix-bound input is explicit:
it is not an assertion that Banaszczyk's analytic theorem has been proved.
The same sign function controls every query and every prefix, and is then
transported back to the original point indexing.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Tusnady.Upper
attribute [local instance] Classical.propDecidable

/-- A finite signed prefix, including the empty and the full prefix. -/
def finitePrefix {N : ℕ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : Fin N → E) (χ : Fin N → ℝ) (k : Fin (N + 1)) : E :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < k), χ i • V i

/-- The filter convention agrees with the `Fin k` convention used by the
signed-series selection theorem. -/
theorem finitePrefix_eq_sum_fin {N : ℕ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : Fin N → E) (χ : Fin N → ℝ) (k : Fin (N + 1)) :
    finitePrefix V χ k = ∑ i : Fin (k : ℕ),
      χ ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩ •
        V ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩ := by
  classical
  symm
  unfold finitePrefix
  refine Finset.sum_bij
    (fun (i : Fin (k : ℕ)) _ =>
      (⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩ : Fin N)) ?_ ?_ ?_ ?_
  · intro i _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact i.isLt
  · intro i _ j _ hij
    exact Fin.ext (congrArg (fun z : Fin N => z.val) hij)
  · intro i hi
    refine ⟨⟨i.val, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro i _
    rfl

@[simp] theorem finitePrefix_zero {N : ℕ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (V : Fin N → E) (χ : Fin N → ℝ) : finitePrefix V χ (0 : Fin (N + 1)) = 0 := by
  simp [finitePrefix]

section Inner
variable {s N : ℕ} {κ E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The projected factorization reconstructs each full orthant sum as the
inner product of one query row and one signed prefix vector. -/
theorem sorted_count_eq_inner_prefix (P : Fin N → Point (s + 1))
    (U : κ → E) (V : Fin N → E) (query : Point s → κ)
    (hfactor : ∀ y i, inner ℝ (U (query y)) (V i) =
      if frontPoint (P (lastSort P i)) ∈ Anchored y then 1 else 0)
    (χ : Fin N → ℝ) (x : Point (s + 1)) :
    realAnchoredCount (fun i => P (lastSort P i)) χ x =
      inner ℝ (U (query (frontPoint x))) (finitePrefix V χ (lastCut P x)) := by
  simp only [realAnchoredCount_eq_sum_ite, finitePrefix, inner_sum,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [sorted_anchored_iff]
  by_cases hf : frontPoint (P (lastSort P i)) ∈ Anchored (frontPoint x) <;>
    by_cases hp : (i : ℕ) < lastCut P x <;> simp [hf, hp, inner_smul_right, hfactor]

/-- One fixed prefix signing implies one coloring for every original orthant.
No distinct-coordinate or injectivity hypothesis is needed in this transfer. -/
theorem coloring_of_projected_prefix_inner_bound (P : Fin N → Point (s + 1))
    (U : κ → E) (V : Fin N → E) (query : Point s → κ)
    (hfactor : ∀ y i, inner ℝ (U (query y)) (V i) =
      if frontPoint (P (lastSort P i)) ∈ Anchored y then 1 else 0)
    (χ : Fin N → ℝ) (hχ : IsSignColoring χ) (B : ℝ)
    (hprefix : ∀ q (k : Fin (N + 1)), |inner ℝ (U q) (finitePrefix V χ k)| ≤ B) :
    ∃ ψ : Fin N → ℝ, IsSignColoring ψ ∧
      ∀ x : Point (s + 1), |realAnchoredCount P ψ x| ≤ B := by
  apply coloring_bound_of_reindex P (lastSort P) χ hχ B
  intro x
  rw [sorted_count_eq_inner_prefix P U V query hfactor χ x]
  exact hprefix _ _

/-- Equivalent discrepancy formulation of the same explicit reduction. -/
theorem pointDiscrepancy_le_of_projected_prefix_inner_bound (P : Fin N → Point (s + 1))
    (U : κ → E) (V : Fin N → E) (query : Point s → κ)
    (hfactor : ∀ y i, inner ℝ (U (query y)) (V i) =
      if frontPoint (P (lastSort P i)) ∈ Anchored y then 1 else 0)
    (χ : Fin N → ℝ) (hχ : IsSignColoring χ) (B : ℝ)
    (hprefix : ∀ q (k : Fin (N + 1)), |inner ℝ (U q) (finitePrefix V χ k)| ≤ B) :
    pointDiscrepancy P ≤ B :=
  (pointDiscrepancy_le_iff_real_colorings P B).mpr
    (coloring_of_projected_prefix_inner_bound P U V query hfactor χ hχ B hprefix)

end Inner
end Tusnady.Upper
