import Tusnady.SparseMixedSamplingData

/-!
# Actual mixed sampling of the concrete sparse space and one L² function

The only external input is the precisely named literature sampling
hypothesis. Basis, enlargement, density, lower bound, good domain and
measure transfer are all supplied by proved constructions.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace Tusnady.SamplingSpace

/-- Concrete mixed sampling. Constants are chosen before d,H and u. The
returned nodes lie in the actual open dyadic-cell domain; repetitions are
still permitted at this stage. Scalar control is for u², so u=sqrt(w)
gives the manuscript's scalar remainder control. -/
theorem sparse_mixed_sampling_from_literature (hLT : Literature.Sampling) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ d H : ℕ, 0 < d →
      ∀ u : (Fin d → ℝ) → ℝ, Measurable u → MemLp u 2 (samplingAmbientMeasure d H) →
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C₁ * (sparseDimension d H + 1 : ℕ) ∧
          ∃ P : Fin m → samplingDomain d H, ∃ a : Fin m → ℝ,
            (∀ j, 0 < a j ∧ a j ≤ 1 / ((m : ℝ) * (((1 : ℝ) / 28) ^ d / 2))) ∧
            (∀ b : Fin (sparseDimension d H) → ℝ,
              C₂ * (∫ x, (∑ i, b i * ambientBasis d H i x) ^ 2 ∂samplingAmbientMeasure d H) ≤
                ∑ j, a j * (∑ i, b i * ambientBasis d H i (P j)) ^ 2 ∧
              (∑ j, a j * (∑ i, b i * ambientBasis d H i (P j)) ^ 2) ≤
                C₃ * (∫ x, (∑ i, b i * ambientBasis d H i x) ^ 2 ∂samplingAmbientMeasure d H)) ∧
            (∑ j, a j * u (P j) ^ 2) ≤ C₃ * (∫ x, u x ^ 2 ∂samplingAmbientMeasure d H) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hs⟩ := MixedSampling.weighted_sampling_from_literature hLT
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro d H hd u humeas hu
  obtain ⟨A⟩ := construct_augmented_data d H hd u humeas hu
  obtain ⟨m, hm, hmc, P, hP⟩ := hs d A.dimension A.dimension_pos A.domain
    (refinedDomain_nonempty d H A.domain A.domain_ae) A.measure
    A.restrictedBasis A.density A.restrictedBasis_measurable
    A.restrictedBasis_product_integrable A.restrictedBasis_inner
    A.density_measurable (A.density_positive hd) A.density_formula
  let Pbase : Fin m → samplingDomain d H := fun j => ⟨P j, A.domain_subset (P j).property⟩
  let a : Fin m → ℝ := MixedSampling.weight A.density P
  have hmbase : (m : ℝ) ≤ C₁ * (sparseDimension d H + 1 : ℕ) := by
    apply hmc.trans
    apply mul_le_mul_of_nonneg_left _ hC₁.le
    exact_mod_cast A.dimension_upper
  refine ⟨m, hm, hmbase, Pbase, a, ?_, ?_, ?_⟩
  · intro j
    exact ⟨MixedSampling.weight_pos hm A.density P (A.density_positive hd) j,
      MixedSampling.weight_le hm A.density P _ (by positivity) (A.density_lower hd) j⟩
  · intro b
    obtain ⟨b', hb'⟩ := A.represents_base b
    have heq : ∀ x : A.domain, (∑ i, b' i * A.restrictedBasis i x) =
        ∑ i, b i * ambientBasis d H i x := fun x => (hb' x x.property).symm
    have h := hP b'
    simp_rw [heq] at h
    have ht := A.integral_transfer (fun x => (∑ i, b i * ambientBasis d H i x) ^ 2)
    rw [ht] at h
    exact h
  · obtain ⟨b, hb⟩ := A.represents_extra
    have heq : ∀ x : A.domain, (∑ i, b i * A.restrictedBasis i x) = u x :=
      fun x => (hb x x.property).symm
    have h := (hP b).2
    simp_rw [heq] at h
    have ht := A.integral_transfer (fun x => u x ^ 2)
    rw [ht] at h
    exact h

end Tusnady.SamplingSpace
