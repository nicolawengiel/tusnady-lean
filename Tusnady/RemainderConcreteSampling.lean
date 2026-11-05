import Tusnady.ConcreteSampling
import Tusnady.RemainderSamplingScalar

/-! The actual remainder density is used in the proved mixed sampler.
There is no unspecified scalar function, basis or sampling assertion. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

lemma samplingDomain_subset_UnitCube {d H : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ samplingDomain d H) : x ∈ UnitCube d :=
  fun k => ⟨(hx.1 k).1, (hx.1 k).2.le⟩

lemma samplingDomain_subset_OpenUnitCube {d H : ℕ} {x : Fin d → ℝ}
    (hx : x ∈ samplingDomain d H) : x ∈ OpenUnitCube d := by
  intro k
  obtain ⟨i, hi⟩ := coordinate_open_cell d H ⟨x, hx⟩ k
  have hl : 0 ≤ DyadicFunctions.dyadicLeft H i := by
    unfold DyadicFunctions.dyadicLeft
    positivity
  exact ⟨hl.trans_lt hi.1, (hx.1 k).2⟩

theorem remainder_concrete_samples (hLT : Literature.Sampling) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ d h : ℕ, 0 < d → ∀ (j : Fin d) (theta : ℝ),
        ∃ m : ℕ, sparseDimension d (h + 3 * d) ≤ m ∧
          (m : ℝ) ≤ C₁ * sparseDimension d (h + 3 * d) ∧
          ∃ A : ConcreteSample d h m C₂ (2 * (28 : ℝ) ^ d),
            Function.Injective (fun k => (A.nodes k : Fin d → ℝ)) ∧
            (∑ k, A.weights k * Witness.cubicEnergyDensity (h := h) j theta (A.nodes k)) ≤
              C₃ * (∫ x, Witness.cubicEnergyDensity (h := h) j theta x ∂Haar.cubeMeasure d) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hs⟩ := concrete_samples_from_literature hLT
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro d h hd j theta
  have hcont := Witness.continuous_remainderSamplingScalar (h := h) hd j theta
  obtain ⟨m, hdm, hmc, A, hinj, ha⟩ := hs d h hd
    (Witness.remainderSamplingScalar (h := h) j theta) hcont.measurable
    (Witness.remainderSamplingScalar_memLp hd j theta (Haar.cubeMeasure d)) hcont.continuousOn
  refine ⟨m, hdm, hmc, A, hinj, ?_⟩
  rw [Witness.integral_remainderSamplingScalar_sq] at ha
  convert ha using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [Witness.remainderSamplingScalar_sq j theta (A.nodes k)
    (samplingDomain_subset_UnitCube (A.nodes k).property)]

end Tusnady.SamplingSpace
