import Tusnady.SamplingDomain
import Tusnady.MixedSampling

/-!
# Concrete normalized sampling data on the actual open-cell domain

The basis, measure and density are constructed from the proved sparse
space. There is no free orthonormal-basis or Christoffel lower-bound input.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace Tusnady.SamplingSpace

abbrev sparseDimension (d H : ℕ) := Fintype.card (SparseIndex d H)

def sparseEnumeration (d H : ℕ) : Fin (sparseDimension d H) ≃ SparseIndex d H :=
  (Fintype.equivFin (SparseIndex d H)).symm

def domainBasis (d H : ℕ) (i : Fin (sparseDimension d H))
    (x : samplingDomain d H) : ℝ := sparseBasis d H (sparseEnumeration d H i) x

lemma domainBasis_measurable (d H : ℕ) (i : Fin (sparseDimension d H)) :
    Measurable (domainBasis d H i) :=
  (sparseBasis_measurable d H _).comp measurable_subtype_coe

lemma domainBasis_product_integrable (d H : ℕ) (i j : Fin (sparseDimension d H)) :
    Integrable (fun x => domainBasis d H i x * domainBasis d H j x) (samplingMeasure d H) := by
  have h := (sparseBasis_product_integrable d H (sparseEnumeration d H i) (sparseEnumeration d H j)).restrict
    (s := samplingDomain d H)
  rw [← map_comap_subtype_coe (samplingDomain_measurable d H)] at h
  exact (MeasurableEmbedding.subtype_coe (samplingDomain_measurable d H)).integrable_map_iff.mp h

lemma domainBasis_inner (d H : ℕ) (i j : Fin (sparseDimension d H)) :
    (∫ x, domainBasis d H i x * domainBasis d H j x ∂samplingMeasure d H) = if i = j then 1 else 0 := by
  have ht := samplingMeasure_integral d H
    (fun x => sparseBasis d H (sparseEnumeration d H i) x * sparseBasis d H (sparseEnumeration d H j) x)
    (fun x hx => by rw [sparseBasis_zero_outside d H _ x hx, zero_mul])
  rw [sparseBasis_inner] at ht
  simpa only [domainBasis, Equiv.apply_eq_iff_eq] using ht

lemma domainBasis_square_sum (d H : ℕ) (x : samplingDomain d H) :
    (∑ i, domainBasis d H i x ^ 2) = sparseChristoffel d H x :=
  (sparseEnumeration d H).sum_comp (fun i => sparseBasis d H i x ^ 2)

lemma sparseDimension_pos (d H : ℕ) (hd : 0 < d) : 0 < sparseDimension d H := by
  simpa only [sparseSpace_finrank] using sparseSpace_finrank_pos d H hd

/-- Actual Christoffel density on Ω, with its nonnegativity included in
the type. The explicit formula is not an additional assumption. -/
def domainDensity (d H : ℕ) (x : samplingDomain d H) : ℝ≥0 :=
  ⟨(1 / (sparseDimension d H : ℝ)) * ∑ i, domainBasis d H i x ^ 2, by positivity⟩

lemma domainDensity_formula (d H : ℕ) (x : samplingDomain d H) :
    (domainDensity d H x : ℝ) =
      (1 / (sparseDimension d H : ℝ)) * ∑ i, domainBasis d H i x ^ 2 := rfl

lemma domainDensity_measurable (d H : ℕ) : Measurable (domainDensity d H) := by
  apply Measurable.subtype_mk
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (domainBasis_measurable d H i).pow_const 2)

/-- The density has the required uniform lower bound, independent of H. -/
theorem domainDensity_lower (d H : ℕ) (hd : 0 < d) (x : samplingDomain d H) :
    ((1 : ℝ) / 28) ^ d ≤ (domainDensity d H x : ℝ) := by
  have hD : (0 : ℝ) < sparseDimension d H := by exact_mod_cast sparseDimension_pos d H hd
  have h := (sparseChristoffel_dimension_bounds d H x (fun k => x.property.1 k)).1
  rw [sparseSpace_finrank] at h
  rw [domainDensity_formula, domainBasis_square_sum]
  calc
    ((1 : ℝ) / 28) ^ d = (1 / (sparseDimension d H : ℝ)) *
        (((1 : ℝ) / 28) ^ d * sparseDimension d H) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)

theorem domainDensity_integrable (d H : ℕ) :
    Integrable (fun x => (domainDensity d H x : ℝ)) (samplingMeasure d H) :=
  MixedSampling.christoffel_density_integrable (samplingMeasure d H) (domainBasis d H)
    (domainDensity d H) (domainBasis_product_integrable d H) (domainDensity_formula d H)

theorem domainDensity_integral (d H : ℕ) (hd : 0 < d) :
    (∫ x, (domainDensity d H x : ℝ) ∂samplingMeasure d H) = 1 :=
  MixedSampling.integral_christoffel_density (samplingMeasure d H) (sparseDimension_pos d H hd)
    (domainBasis d H) (domainDensity d H) (domainBasis_product_integrable d H)
    (domainBasis_inner d H) (domainDensity_formula d H)

/-- A genuine literature sampling application with all sparse-space
basis, measure and density data discharged by the concrete constructions.
The constants C₁,C₂,C₃ are chosen before d and H. The returned list may
still have repetitions; adding the extra function is a separate next step. -/
theorem sparse_weighted_sampling_from_literature (hLT : Literature.Sampling) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ d H : ℕ, 0 < d →
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C₁ * (sparseDimension d H : ℝ) ∧
          ∃ P : Fin m → samplingDomain d H,
            (∀ i, 0 < MixedSampling.weight (domainDensity d H) P i ∧
              MixedSampling.weight (domainDensity d H) P i ≤
                1 / ((m : ℝ) * ((1 : ℝ) / 28) ^ d)) ∧
            ∀ a : Fin (sparseDimension d H) → ℝ,
              C₂ * (∫ x, (∑ i, a i * domainBasis d H i x) ^ 2 ∂samplingMeasure d H) ≤
                ∑ j, MixedSampling.weight (domainDensity d H) P j *
                  (∑ i, a i * domainBasis d H i (P j)) ^ 2 ∧
              (∑ j, MixedSampling.weight (domainDensity d H) P j *
                  (∑ i, a i * domainBasis d H i (P j)) ^ 2) ≤
                C₃ * (∫ x, (∑ i, a i * domainBasis d H i x) ^ 2 ∂samplingMeasure d H) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hs⟩ := MixedSampling.weighted_sampling_from_literature hLT
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro d H hd
  have hρ : ∀ x : samplingDomain d H, 0 < domainDensity d H x := by
    intro x
    exact_mod_cast lt_of_lt_of_le (by positivity : (0 : ℝ) < ((1 : ℝ) / 28) ^ d)
      (domainDensity_lower d H hd x)
  obtain ⟨m, hm, hmc, P, hP⟩ := hs d (sparseDimension d H) (sparseDimension_pos d H hd)
    (samplingDomain d H) (samplingDomain_nonempty d H) (samplingMeasure d H)
    (domainBasis d H) (domainDensity d H) (domainBasis_measurable d H)
    (domainBasis_product_integrable d H) (domainBasis_inner d H)
    (domainDensity_measurable d H) hρ (domainDensity_formula d H)
  refine ⟨m, hm, hmc, P, ?_, hP⟩
  intro i
  exact ⟨MixedSampling.weight_pos hm _ P hρ i,
    MixedSampling.weight_le hm _ P _ (by positivity) (domainDensity_lower d H hd) i⟩

end Tusnady.SamplingSpace
