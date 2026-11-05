import Tusnady.SamplingRefinement
import Tusnady.OneFunctionExtension

/-!
# Constructing the actual one-function extension of the sparse sampling space

This module proves existence of all finite basis data used subsequently.
The data structure is an internal constructed result, not a literature or
main-theorem assumption. The zero-energy branch uses an explicitly proved
full-measure refinement, so a.e. equality is not silently made pointwise.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace Tusnady.SamplingSpace
open OneFunctionExtension

structure AugmentedData (d H : ℕ) (u : (Fin d → ℝ) → ℝ) where
  domain : Set (Fin d → ℝ)
  measurable_domain : MeasurableSet domain
  domain_subset : domain ⊆ samplingDomain d H
  domain_ae : domain =ᵐ[productVolume d] samplingDomain d H
  dimension : ℕ
  dimension_pos : 0 < dimension
  dimension_lower : sparseDimension d H ≤ dimension
  dimension_upper : dimension ≤ sparseDimension d H + 1
  basis : Fin dimension → (Fin d → ℝ) → ℝ
  basis_measurable : ∀ i, Measurable (basis i)
  basis_memLp : ∀ i, MemLp (basis i) 2 (samplingAmbientMeasure d H)
  basis_inner : ∀ i j, (∫ x, basis i x * basis j x ∂samplingAmbientMeasure d H) =
    if i = j then 1 else 0
  square_sum_lower : ∀ x ∈ domain,
    ((1 : ℝ) / 28) ^ d * (sparseDimension d H : ℝ) ≤ ∑ i, basis i x ^ 2
  represents_base : ∀ a : Fin (sparseDimension d H) → ℝ,
    ∃ b : Fin dimension → ℝ, ∀ x ∈ domain,
      (∑ i, a i * ambientBasis d H i x) = ∑ i, b i * basis i x
  represents_extra : ∃ b : Fin dimension → ℝ, ∀ x ∈ domain, u x = ∑ i, b i * basis i x

/-- The actual concrete sparse family has the uniform square-sum bound
on every point of the actual open-cell domain. -/
lemma ambientBasis_square_sum_lower (d H : ℕ) (x : Fin d → ℝ)
    (hx : x ∈ samplingDomain d H) :
    ((1 : ℝ) / 28) ^ d * (sparseDimension d H : ℝ) ≤ ∑ i, ambientBasis d H i x ^ 2 := by
  have h := (sparseChristoffel_dimension_bounds d H x (fun k => hx.1 k)).1
  simpa only [sparseSpace_finrank, ambientBasis_square_sum] using h

/-- Explicit Gram--Schmidt produces the enlarged orthonormal family from
an arbitrary measurable L² function, with no free basis assumption. -/
theorem construct_augmented_data (d H : ℕ) (hd : 0 < d)
    (u : (Fin d → ℝ) → ℝ) (humeas : Measurable u)
    (hu : MemLp u 2 (samplingAmbientMeasure d H)) : Nonempty (AugmentedData d H u) := by
  classical
  let μ := samplingAmbientMeasure d H
  let φ := ambientBasis d H
  let r := residual μ φ u
  have hφ : ∀ i, MemLp (φ i) 2 μ := ambientBasis_memLp d H
  have hφmeas : ∀ i, Measurable (φ i) := ambientBasis_measurable d H
  have hφorth : ∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0 := ambientBasis_inner d H
  by_cases he : energy μ φ u = 0
  · have hrmeas : Measurable r := residual_measurable μ φ u hφmeas humeas
    have hrae : r =ᵐ[μ] 0 := residual_ae_zero_of_energy_zero μ φ u hφ hu he
    refine ⟨{
      domain := refinedDomain d H r
      measurable_domain := refinedDomain_measurable d H r hrmeas
      domain_subset := fun _ hx => hx.1
      domain_ae := refinedDomain_ae d H r hrae
      dimension := sparseDimension d H
      dimension_pos := sparseDimension_pos d H hd
      dimension_lower := le_rfl
      dimension_upper := Nat.le_succ _
      basis := φ
      basis_measurable := hφmeas
      basis_memLp := hφ
      basis_inner := hφorth
      square_sum_lower := ?_
      represents_base := ?_
      represents_extra := ?_ }⟩
    · intro x hx
      exact ambientBasis_square_sum_lower d H x hx.1
    · intro a
      exact ⟨a, fun _ _ => rfl⟩
    · refine ⟨coefficient μ φ u, ?_⟩
      intro x hx
      exact sub_eq_zero.mp hx.2
  · have hep : 0 < energy μ φ u := lt_of_le_of_ne (energy_nonneg μ φ u) (Ne.symm he)
    refine ⟨{
      domain := samplingDomain d H
      measurable_domain := samplingDomain_measurable d H
      domain_subset := fun _ hx => hx
      domain_ae := Filter.EventuallyEq.rfl
      dimension := sparseDimension d H + 1
      dimension_pos := Nat.succ_pos _
      dimension_lower := Nat.le_succ _
      dimension_upper := le_rfl
      basis := extendedBasis μ φ u
      basis_measurable := extendedBasis_measurable μ φ u hφmeas humeas
      basis_memLp := extendedBasis_memLp μ φ u hφ hu
      basis_inner := extendedBasis_inner μ φ u hφ hu hφorth hep
      square_sum_lower := ?_
      represents_base := ?_
      represents_extra := ?_ }⟩
    · intro x hx
      rw [extendedBasis_square_sum]
      exact (ambientBasis_square_sum_lower d H x hx).trans (le_add_of_nonneg_left (sq_nonneg _))
    · intro a
      refine ⟨Fin.cons (0 : ℝ) a, ?_⟩
      intro x _
      exact (original_combination_in_extension μ φ u a x).symm
    · refine ⟨Fin.cons (Real.sqrt (energy μ φ u)) (coefficient μ φ u), ?_⟩
      intro x _
      exact (function_in_extension μ φ u hep x).symm

end Tusnady.SamplingSpace
