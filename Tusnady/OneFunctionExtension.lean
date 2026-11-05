import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Explicit Gram--Schmidt adjoining of one actual function

Coefficients, residual and normalization are actual Bochner integrals and
pointwise functions. This generic calculation will be instantiated with
the concrete sparse-cross basis; it does not postulate a new basis.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.OneFunctionExtension

variable {α : Type*} [MeasurableSpace α] {D : ℕ}

def coefficient (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) (i : Fin D) : ℝ :=
  ∫ x, φ i x * u x ∂μ

def projection (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) (x : α) : ℝ :=
  ∑ i, coefficient μ φ u i * φ i x

def residual (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) : α → ℝ :=
  fun x => u x - projection μ φ u x

def energy (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) : ℝ :=
  ∫ x, residual μ φ u x ^ 2 ∂μ

def extra (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) : α → ℝ :=
  fun x => residual μ φ u x / Real.sqrt (energy μ φ u)

lemma projection_memLp (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) : MemLp (projection μ φ u) 2 μ :=
  memLp_finset_sum _ (fun i _ => (hφ i).const_smul (coefficient μ φ u i))

lemma residual_memLp (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ) : MemLp (residual μ φ u) 2 μ :=
  hu.sub (projection_memLp μ φ u hφ)

lemma residual_measurable (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, Measurable (φ i)) (hu : Measurable u) : Measurable (residual μ φ u) :=
  hu.sub (Finset.measurable_sum _ fun i _ => measurable_const.mul (hφ i))

lemma extra_measurable (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, Measurable (φ i)) (hu : Measurable u) : Measurable (extra μ φ u) :=
  (residual_measurable μ φ u hφ hu).div_const _

lemma extra_memLp (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ) : MemLp (extra μ φ u) 2 μ := by
  convert (residual_memLp μ φ u hφ hu).const_smul (Real.sqrt (energy μ φ u))⁻¹ using 1
  funext x
  simp only [extra, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The actual Gram--Schmidt residual is orthogonal by direct integration. -/
theorem residual_orthogonal (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ)
    (horth : ∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0) (i : Fin D) :
    (∫ x, φ i x * residual μ φ u x ∂μ) = 0 := by
  classical
  have hsum : ∀ j : Fin D, Integrable
      (fun x => coefficient μ φ u j * (φ i x * φ j x)) μ :=
    fun j => ((hφ i).integrable_mul (hφ j)).const_mul _
  have hf : (fun x => φ i x * residual μ φ u x) =
      (fun x => φ i x * u x - ∑ j, coefficient μ φ u j * (φ i x * φ j x)) := by
    funext x
    unfold residual projection
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hui : Integrable (fun x => φ i x * u x) μ := (hφ i).integrable_mul hu
  have hsi : Integrable (fun x => ∑ j, coefficient μ φ u j * (φ i x * φ j x)) μ :=
    integrable_finset_sum Finset.univ (fun j _ => hsum j)
  rw [hf, integral_sub hui hsi, integral_finset_sum Finset.univ (fun j _ => hsum j)]
  simp only [integral_const_mul, horth]
  simp [coefficient]

lemma energy_nonneg (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) :
    0 ≤ energy μ φ u := integral_nonneg (fun _ => sq_nonneg _)

/-- Zero residual energy gives an actual a.e. identity. The later sampling
domain is explicitly refined by this identity in the zero-energy branch. -/
theorem residual_ae_zero_of_energy_zero (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ) (he : energy μ φ u = 0) :
    residual μ φ u =ᵐ[μ] 0 := by
  have hr := residual_memLp μ φ u hφ hu
  have hi : Integrable (fun x => residual μ φ u x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hr.aestronglyMeasurable).mp hr
  have hz := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun x => sq_nonneg
    (residual μ φ u x))) hi).mp he
  filter_upwards [hz] with x hx
  exact sq_eq_zero_iff.mp hx

theorem extra_orthogonal (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ)
    (horth : ∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0) (i : Fin D) :
    (∫ x, φ i x * extra μ φ u x ∂μ) = 0 := by
  have hf : (fun x => φ i x * extra μ φ u x) =
      (fun x => (φ i x * residual μ φ u x) / Real.sqrt (energy μ φ u)) := by
    funext x
    unfold extra
    ring
  rw [hf, integral_div, residual_orthogonal μ φ u hφ hu horth]
  simp

theorem extra_normalized (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (he : 0 < energy μ φ u) : (∫ x, extra μ φ u x * extra μ φ u x ∂μ) = 1 := by
  have hs := Real.sq_sqrt he.le
  have hf : (fun x => extra μ φ u x * extra μ φ u x) =
      (fun x => residual μ φ u x ^ 2 / energy μ φ u) := by
    funext x
    unfold extra
    rw [← pow_two, div_pow, hs]
  rw [hf, integral_div]
  exact div_self he.ne'

/-- The additional function is in the constructed span pointwise whenever
the extra direction is present. -/
theorem function_decomposition (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (he : 0 < energy μ φ u) (x : α) :
    u x = projection μ φ u x + Real.sqrt (energy μ φ u) * extra μ φ u x := by
  have hn : Real.sqrt (energy μ φ u) ≠ 0 := (Real.sqrt_pos.mpr he).ne'
  unfold extra residual
  field_simp
  ring

/-- The enlarged family is explicitly the normalized residual followed
by the original D functions. -/
def extendedBasis (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) :
    Fin (D + 1) → α → ℝ := Fin.cons (extra μ φ u) φ

theorem extendedBasis_memLp (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ) :
    ∀ i, MemLp (extendedBasis μ φ u i) 2 μ := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact extra_memLp μ φ u hφ hu
  · exact hφ j

theorem extendedBasis_measurable (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, Measurable (φ i)) (hu : Measurable u) :
    ∀ i, Measurable (extendedBasis μ φ u i) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact extra_measurable μ φ u hφ hu
  · exact hφ j

theorem extendedBasis_product_integrable (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ) (i j : Fin (D + 1)) :
    Integrable (fun x => extendedBasis μ φ u i x * extendedBasis μ φ u j x) μ :=
  (extendedBasis_memLp μ φ u hφ hu i).integrable_mul (extendedBasis_memLp μ φ u hφ hu j)

/-- The entire explicitly adjoined family is orthonormal when the
computed residual energy is positive. -/
theorem extendedBasis_inner (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ) (hu : MemLp u 2 μ)
    (horth : ∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0)
    (he : 0 < energy μ φ u) (i j : Fin (D + 1)) :
    (∫ x, extendedBasis μ φ u i x * extendedBasis μ φ u j x ∂μ) = if i = j then 1 else 0 := by
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa [extendedBasis] using extra_normalized μ φ u he
    · have h := extra_orthogonal μ φ u hφ hu horth j
      simpa [extendedBasis, mul_comm] using h
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa [extendedBasis] using extra_orthogonal μ φ u hφ hu horth i
    · simpa [extendedBasis] using horth i j

theorem extendedBasis_square_sum (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ) (x : α) :
    (∑ i, extendedBasis μ φ u i x ^ 2) = extra μ φ u x ^ 2 + ∑ i, φ i x ^ 2 := by
  simp only [Fin.sum_univ_succ, extendedBasis, Fin.cons_zero, Fin.cons_succ]

theorem original_combination_in_extension (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (a : Fin D → ℝ) (x : α) :
    (∑ i : Fin (D + 1), (Fin.cons (0 : ℝ) a : Fin (D + 1) → ℝ) i * extendedBasis μ φ u i x) = ∑ i, a i * φ i x := by
  simp [Fin.sum_univ_succ, extendedBasis]

theorem function_in_extension (μ : Measure α) (φ : Fin D → α → ℝ) (u : α → ℝ)
    (he : 0 < energy μ φ u) (x : α) :
    (∑ i : Fin (D + 1), (Fin.cons (Real.sqrt (energy μ φ u)) (coefficient μ φ u) : Fin (D + 1) → ℝ) i *
      extendedBasis μ φ u i x) = u x := by
  rw [Fin.sum_univ_succ]
  simpa [extendedBasis, projection, add_comm] using (function_decomposition μ φ u he x).symm

end Tusnady.OneFunctionExtension
