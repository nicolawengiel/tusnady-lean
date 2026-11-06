import Tusnady.SamplingSpaceChristoffel
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Actual tensor products of the canonical affine detail basis

These are actual functions on real coordinate vectors, integrated against
actual product Lebesgue measure. Tensor orthonormality and Christoffel
multiplicativity follow from proved univariate data and mathlib Fubini.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

def productVolume (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => (volume : Measure ℝ))

abbrev TensorIndex {d : ℕ} (ℓ : Fin d → ℕ) :=
  ∀ k : Fin d, Fin (Module.finrank ℝ (detailSpace (ℓ k)))

def tensorBasis {d : ℕ} (ℓ : Fin d → ℕ) (i : TensorIndex ℓ) (x : Fin d → ℝ) : ℝ :=
  ∏ k, detailBasis (ℓ k) (i k) (x k)

theorem tensorBasis_measurable {d : ℕ} (ℓ : Fin d → ℕ) (i : TensorIndex ℓ) :
    Measurable (tensorBasis ℓ i) :=
  Finset.measurable_prod _ fun k _ => (detailBasis_measurable (ℓ k) (i k)).comp (measurable_pi_apply k)

lemma tensorBasis_product_eq {d : ℕ} (ℓ m : Fin d → ℕ)
    (i : TensorIndex ℓ) (l : TensorIndex m) :
    (fun x => tensorBasis ℓ i x * tensorBasis m l x) =
      (fun x => ∏ k, detailBasis (ℓ k) (i k) (x k) * detailBasis (m k) (l k) (x k)) := by
  funext x
  exact (Finset.prod_mul_distrib).symm

theorem tensorBasis_product_integrable {d : ℕ} (ℓ m : Fin d → ℕ)
    (i : TensorIndex ℓ) (l : TensorIndex m) :
    Integrable (fun x => tensorBasis ℓ i x * tensorBasis m l x) (productVolume d) := by
  rw [tensorBasis_product_eq]
  exact Integrable.fintype_prod (fun k => detailBasis_product_integrable (ℓ k) (m k) (i k) (l k))

theorem tensorBasis_memLp {d : ℕ} (ℓ : Fin d → ℕ) (i : TensorIndex ℓ) :
    MemLp (tensorBasis ℓ i) 2 (productVolume d) := by
  apply (memLp_two_iff_integrable_sq (tensorBasis_measurable ℓ i).aestronglyMeasurable).mpr
  simpa only [pow_two] using tensorBasis_product_integrable ℓ ℓ i i

/-- Actual tensor orthonormality within one level vector. -/
theorem tensorBasis_inner {d : ℕ} (ℓ : Fin d → ℕ) (i l : TensorIndex ℓ) :
    (∫ x, tensorBasis ℓ i x * tensorBasis ℓ l x ∂productVolume d) = if i = l then 1 else 0 := by
  classical
  rw [tensorBasis_product_eq]
  unfold productVolume
  rw [integral_fintype_prod_eq_prod (fun k t => detailBasis (ℓ k) (i k) t * detailBasis (ℓ k) (l k) t)]
  simp_rw [detailBasis_inner]
  by_cases h : i = l
  · subst l
    simp
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])]
    simp [h]

/-- Different multi-levels are orthogonal by a genuine differing coordinate. -/
theorem tensorBasis_inner_interlevel {d : ℕ} {ℓ m : Fin d → ℕ} (hℓm : ℓ ≠ m)
    (i : TensorIndex ℓ) (l : TensorIndex m) :
    (∫ x, tensorBasis ℓ i x * tensorBasis m l x ∂productVolume d) = 0 := by
  classical
  rw [tensorBasis_product_eq]
  unfold productVolume
  rw [integral_fintype_prod_eq_prod (fun k t => detailBasis (ℓ k) (i k) t * detailBasis (m k) (l k) t)]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hℓm
  exact Finset.prod_eq_zero (Finset.mem_univ k) (detailBasis_inner_interlevel hk (i k) (l k))

/-- Exact tensor dimension before any asymptotic estimate. -/
theorem tensorIndex_card {d : ℕ} (ℓ : Fin d → ℕ) :
    Fintype.card (TensorIndex ℓ) = ∏ k, Module.finrank ℝ (detailSpace (ℓ k)) := by
  simp only [TensorIndex, Fintype.card_pi, Fintype.card_fin]

/-- Genuine Christoffel multiplicativity for the canonical tensor basis. -/
theorem tensorBasis_square_sum {d : ℕ} (ℓ : Fin d → ℕ) (x : Fin d → ℝ) :
    (∑ i : TensorIndex ℓ, tensorBasis ℓ i x ^ 2) = ∏ k, detailChristoffel (ℓ k) (x k) := by
  classical
  simp only [tensorBasis, ← Finset.prod_pow, detailChristoffel_basis_sum]
  exact (Fintype.prod_sum (fun k i => detailBasis (ℓ k) i (x k) ^ 2)).symm

theorem detailSpace_finrank_bounds (j : ℕ) :
    2 ^ j ≤ Module.finrank ℝ (detailSpace j) ∧
      Module.finrank ℝ (detailSpace j) ≤ 2 * 2 ^ j := by
  cases j with
  | zero => rw [detailSpace_zero_finrank]; norm_num
  | succ j =>
    rw [detailSpace_succ_finrank]
    exact ⟨le_rfl, by omega⟩

/-- Relative bounds against the actual detail dimension. -/
theorem detailChristoffel_dimension_bounds (j : ℕ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
    ((1 : ℝ) / 28) * (Module.finrank ℝ (detailSpace j) : ℝ) ≤ detailChristoffel j t ∧
      detailChristoffel j t ≤ 4 * (Module.finrank ℝ (detailSpace j) : ℝ) := by
  have hd := detailSpace_finrank_bounds j
  have hdlo : (2 : ℝ) ^ j ≤ (Module.finrank ℝ (detailSpace j) : ℝ) := by exact_mod_cast hd.1
  have hdhi : (Module.finrank ℝ (detailSpace j) : ℝ) ≤ 2 * (2 : ℝ) ^ j := by exact_mod_cast hd.2
  have hc := detailChristoffel_bounds j t ht
  constructor <;> nlinarith [hc.1, hc.2]

/-- Relative tensor-Christoffel bounds with constants depending only on
the number of coordinates, before any level-counting argument. -/
theorem tensorBasis_dimension_bounds {d : ℕ} (ℓ : Fin d → ℕ) (x : Fin d → ℝ)
    (hx : ∀ k, x k ∈ Ico (0 : ℝ) 1) :
    ((1 : ℝ) / 28) ^ d * (Fintype.card (TensorIndex ℓ) : ℝ) ≤
        (∑ i : TensorIndex ℓ, tensorBasis ℓ i x ^ 2) ∧
      (∑ i : TensorIndex ℓ, tensorBasis ℓ i x ^ 2) ≤
        (4 : ℝ) ^ d * (Fintype.card (TensorIndex ℓ) : ℝ) := by
  rw [tensorBasis_square_sum, tensorIndex_card, Nat.cast_prod]
  have hlo : (∏ k : Fin d, ((1 : ℝ) / 28) * (Module.finrank ℝ (detailSpace (ℓ k)) : ℝ)) ≤
      ∏ k : Fin d, detailChristoffel (ℓ k) (x k) := by
    apply Finset.prod_le_prod₀
    · intro k _
      positivity
    · intro k _
      exact (detailChristoffel_dimension_bounds (ℓ k) (x k) (hx k)).1
  have hhi : (∏ k : Fin d, detailChristoffel (ℓ k) (x k)) ≤
      ∏ k : Fin d, (4 : ℝ) * (Module.finrank ℝ (detailSpace (ℓ k)) : ℝ) := by
    apply Finset.prod_le_prod₀
    · intro k _
      exact sq_nonneg _
    · intro k _
      exact (detailChristoffel_dimension_bounds (ℓ k) (x k) (hx k)).2
  exact ⟨by simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using hlo,
    by simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hhi⟩

end Tusnady.SamplingSpace
