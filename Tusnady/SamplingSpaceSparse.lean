import Tusnady.SamplingSpaceTensor

/-!
# The actual finite sparse-cross sampling basis

The index set contains precisely the nonnegative multi-levels of total
level at most H, and all canonical tensor detail modes at each such level.
The finite L² span and its dimension are constructed from this actual
orthonormal family.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

/-- Bounded natural levels; the sum constraint implies the coordinate
bounds, so this is precisely the manuscript's finite sparse cross. -/
abbrev Levels (d H : ℕ) :=
  {ℓ : Fin d → Fin (H + 1) // ∑ k, (ℓ k).val ≤ H}

def levelDepth {d H : ℕ} (ℓ : Levels d H) : Fin d → ℕ := fun k => (ℓ.val k).val

theorem levelDepth_injective (d H : ℕ) : Function.Injective (@levelDepth d H) := by
  intro ℓ m h
  apply Subtype.ext
  funext k
  apply Fin.ext
  exact congrFun h k

abbrev SparseIndex (d H : ℕ) := Σ ℓ : Levels d H, TensorIndex (levelDepth ℓ)

def sparseBasis (d H : ℕ) (i : SparseIndex d H) : (Fin d → ℝ) → ℝ :=
  tensorBasis (levelDepth i.1) i.2

theorem sparseBasis_measurable (d H : ℕ) (i : SparseIndex d H) :
    Measurable (sparseBasis d H i) := tensorBasis_measurable _ _

theorem sparseBasis_memLp (d H : ℕ) (i : SparseIndex d H) :
    MemLp (sparseBasis d H i) 2 (productVolume d) := tensorBasis_memLp _ _

theorem sparseBasis_product_integrable (d H : ℕ) (i l : SparseIndex d H) :
    Integrable (fun x => sparseBasis d H i x * sparseBasis d H l x) (productVolume d) :=
  tensorBasis_product_integrable _ _ _ _

/-- Actual orthonormality on the complete finite sparse-cross basis. -/
theorem sparseBasis_inner (d H : ℕ) (i l : SparseIndex d H) :
    (∫ x, sparseBasis d H i x * sparseBasis d H l x ∂productVolume d) = if i = l then 1 else 0 := by
  classical
  obtain ⟨ℓ, i⟩ := i
  obtain ⟨m, l⟩ := l
  by_cases h : ℓ = m
  · subst m
    simpa only [sparseBasis, Sigma.mk.inj_iff, heq_eq_eq, true_and] using
      tensorBasis_inner (levelDepth ℓ) i l
  · have hd : levelDepth ℓ ≠ levelDepth m := fun hh => h (levelDepth_injective d H hh)
    have hz := tensorBasis_inner_interlevel hd i l
    simpa [sparseBasis, h] using hz

def sparseBasisL2 (d H : ℕ) (i : SparseIndex d H) : Lp ℝ 2 (productVolume d) :=
  (sparseBasis_memLp d H i).toLp (sparseBasis d H i)

lemma sparseBasisL2_ae (d H : ℕ) (i : SparseIndex d H) :
    sparseBasisL2 d H i =ᵐ[productVolume d] sparseBasis d H i :=
  (sparseBasis_memLp d H i).coeFn_toLp

theorem sparseBasisL2_orthonormal (d H : ℕ) : Orthonormal ℝ (sparseBasisL2 d H) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i l
  rw [L2.inner_def]
  calc
    _ = ∫ x, sparseBasis d H i x * sparseBasis d H l x ∂productVolume d := by
      apply integral_congr_ae
      filter_upwards [sparseBasisL2_ae d H i, sparseBasisL2_ae d H l] with x hi hl
      rw [hi, hl]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = _ := sparseBasis_inner d H i l

/-- The genuine manuscript sparse-cross L² subspace. -/
def sparseSpace (d H : ℕ) : Submodule ℝ (Lp ℝ 2 (productVolume d)) :=
  Submodule.span ℝ (Set.range (sparseBasisL2 d H))

instance sparseSpace_finiteDimensional (d H : ℕ) : FiniteDimensional ℝ (sparseSpace d H) := by
  unfold sparseSpace
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem sparseSpace_finrank (d H : ℕ) :
    Module.finrank ℝ (sparseSpace d H) = Fintype.card (SparseIndex d H) :=
  finrank_span_eq_card (sparseBasisL2_orthonormal d H).linearIndependent

/-- Exact sparse-cross dimension as a sum of actual tensor dimensions. -/
theorem sparseIndex_card (d H : ℕ) :
    Fintype.card (SparseIndex d H) = ∑ ℓ : Levels d H, ∏ k, Module.finrank ℝ (detailSpace (levelDepth ℓ k)) := by
  simp only [SparseIndex, Fintype.card_sigma, tensorIndex_card]

def sparseChristoffel (d H : ℕ) (x : Fin d → ℝ) : ℝ :=
  ∑ i : SparseIndex d H, sparseBasis d H i x ^ 2

theorem sparseChristoffel_sum (d H : ℕ) (x : Fin d → ℝ) :
    sparseChristoffel d H x = ∑ ℓ : Levels d H, ∏ k, detailChristoffel (levelDepth ℓ k) (x k) := by
  simp only [sparseChristoffel, Fintype.sum_sigma, sparseBasis, tensorBasis_square_sum]

/-- Pointwise lower/upper Christoffel bounds relative to the actual
sparse-cross dimension, with constants independent of H and x. -/
theorem sparseChristoffel_dimension_bounds (d H : ℕ) (x : Fin d → ℝ)
    (hx : ∀ k, x k ∈ Ico (0 : ℝ) 1) :
    ((1 : ℝ) / 28) ^ d * (Module.finrank ℝ (sparseSpace d H) : ℝ) ≤ sparseChristoffel d H x ∧
      sparseChristoffel d H x ≤ (4 : ℝ) ^ d * (Module.finrank ℝ (sparseSpace d H) : ℝ) := by
  rw [sparseSpace_finrank, Fintype.card_sigma, Nat.cast_sum, sparseChristoffel, Fintype.sum_sigma]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ _
    exact (tensorBasis_dimension_bounds (levelDepth ℓ) x hx).1
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ _
    exact (tensorBasis_dimension_bounds (levelDepth ℓ) x hx).2

end Tusnady.SamplingSpace
