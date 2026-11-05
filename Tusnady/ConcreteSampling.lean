import Tusnady.ConcreteGram
import Tusnady.SparseMixedDistinct

/-! Construction of genuine Gram sampling data from the explicitly named
literature theorem, with all concrete basis and measure facts discharged. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

theorem concrete_samples_from_literature (hLT : Literature.Sampling) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ d h : ℕ, 0 < d →
      ∀ u : (Fin d → ℝ) → ℝ, Measurable u → MemLp u 2 (Haar.cubeMeasure d) →
        ContinuousOn u (samplingDomain d (h + 3 * d)) →
        ∃ m : ℕ, sparseDimension d (h + 3 * d) ≤ m ∧
          (m : ℝ) ≤ C₁ * sparseDimension d (h + 3 * d) ∧
          ∃ A : ConcreteSample d h m C₂ (2 * (28 : ℝ) ^ d),
            Function.Injective (fun j => (A.nodes j : Fin d → ℝ)) ∧
            (∑ j, A.weights j * u (A.nodes j) ^ 2) ≤
              C₃ * (∫ x, u x ^ 2 ∂Haar.cubeMeasure d) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hs⟩ := sparse_mixed_distinct_sampling hLT
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro d h hd u humeas hu huc
  rw [← samplingAmbientMeasure_eq_cubeMeasure d (h + 3 * d)] at hu
  obtain ⟨m, hdm, hm, hmc, P, a, hinj, ha, hnorm, huscalar⟩ :=
    hs d (h + 3 * d) hd u humeas hu huc
  have hwbound : ∀ j, a j ≤ (2 * (28 : ℝ) ^ d) / m := by
    intro j
    have hi : 1 / ((m : ℝ) * (((1 : ℝ) / 28) ^ d / 2)) =
        (2 * (28 : ℝ) ^ d) / m := by
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [div_pow]
      simp only [one_pow]
      field_simp
    rw [← hi]
    exact (ha j).2
  have hn : ∀ b : Fin (sparseDimension d (h + 3 * d)) → ℝ,
      (∫ x, (∑ i, b i * ambientBasis d (h + 3 * d) i x) ^ 2
        ∂samplingAmbientMeasure d (h + 3 * d)) = ∑ i, b i ^ 2 :=
    FiniteSamplingAnalysis.integral_combination_sq _ _ (ambientBasis_memLp _ _)
      (ambientBasis_inner _ _)
  let A : ConcreteSample d h m C₂ (2 * (28 : ℝ) ^ d) := {
    nodes := P
    weights := a
    count_pos := hm
    lower_pos := hC₂
    bound_pos := by positivity
    weight_nonneg := fun j => (ha j).1.le
    weight_upper := hwbound
    sampling_lower := fun b => by simpa only [hn b] using (hnorm b).1 }
  refine ⟨m, hdm, hmc, A, hinj, ?_⟩
  simpa only [samplingAmbientMeasure_eq_cubeMeasure] using huscalar

end Tusnady.SamplingSpace
