import Tusnady.SamplingContinuity
import Tusnady.FiniteSamplingPerturbation

/-! Actual mixed sampling with pairwise distinct nodes. The original
positive weights remain fixed under perturbation. Only continuity of the
additional actual function on the open cell domain remains an input. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators NNReal ENNReal Topology
namespace Tusnady.SamplingSpace
open FiniteSamplingAnalysis

theorem sparse_mixed_distinct_sampling (hLT : Literature.Sampling) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ d H : ℕ, 0 < d →
      ∀ u : (Fin d → ℝ) → ℝ, Measurable u → MemLp u 2 (samplingAmbientMeasure d H) →
        ContinuousOn u (samplingDomain d H) →
        ∃ m : ℕ, sparseDimension d H ≤ m ∧ 0 < m ∧
          (m : ℝ) ≤ C₁ * sparseDimension d H ∧
          ∃ P : Fin m → samplingDomain d H, ∃ a : Fin m → ℝ,
            Function.Injective (fun j => (P j : Fin d → ℝ)) ∧
            (∀ j, 0 < a j ∧ a j ≤ 1 / ((m : ℝ) * (((1 : ℝ) / 28) ^ d / 2))) ∧
            (∀ b : Fin (sparseDimension d H) → ℝ,
              C₂ * (∫ x, (∑ i, b i * ambientBasis d H i x) ^ 2 ∂samplingAmbientMeasure d H) ≤
                ∑ j, a j * (∑ i, b i * ambientBasis d H i (P j)) ^ 2 ∧
              (∑ j, a j * (∑ i, b i * ambientBasis d H i (P j)) ^ 2) ≤
                C₃ * (∫ x, (∑ i, b i * ambientBasis d H i x) ^ 2 ∂samplingAmbientMeasure d H)) ∧
            (∑ j, a j * u (P j) ^ 2) ≤ C₃ * (∫ x, u x ^ 2 ∂samplingAmbientMeasure d H) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hs⟩ := sparse_mixed_sampling_from_literature hLT
  refine ⟨2 * C₁, C₂ / 2, 2 * C₃, by positivity, by positivity, by positivity, ?_⟩
  intro d H hd u humeas hu huc
  obtain ⟨m, hm, hmc, P, a, ha, hP, huP⟩ := hs d H hd u humeas hu
  let φ : Fin (sparseDimension d H) → samplingDomain d H → ℝ :=
    fun i x => ambientBasis d H i x
  have hn : ∀ b : Fin (sparseDimension d H) → ℝ,
      (∫ x, (∑ i, b i * ambientBasis d H i x) ^ 2 ∂samplingAmbientMeasure d H) =
        ∑ i, b i ^ 2 :=
    integral_combination_sq _ _ (ambientBasis_memLp d H) (ambientBasis_inner d H)
  have hP' : ∀ b, C₂ * (∑ i, b i ^ 2) ≤ empirical φ a P b ∧
      empirical φ a P b ≤ C₃ * (∑ i, b i ^ 2) := by
    intro b
    simpa only [hn b] using hP b
  have hDm := dimension_le_sample_count φ a P hC₂ (fun b => (hP' b).1)
  have hmc' : (m : ℝ) ≤ (2 * C₁) * sparseDimension d H := by
    have hD : (1 : ℝ) ≤ sparseDimension d H := by
      exact_mod_cast sparseDimension_pos d H hd
    have hmc'' : (m : ℝ) ≤ C₁ * ((sparseDimension d H : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hmc
    nlinarith
  let I : ℝ := ∫ x, u x ^ 2 ∂samplingAmbientMeasure d H
  have hI : 0 ≤ I := integral_nonneg fun x => sq_nonneg (u x)
  let scalar : (Fin m → samplingDomain d H) → ℝ := fun Q => ∑ j, a j * u (Q j) ^ 2
  have hscalar : Continuous scalar := by
    apply continuous_finset_sum
    intro j _
    exact continuous_const.mul (((huc.restrict).comp (continuous_apply j)).pow 2)
  have hV : ∃ V : Set (Fin m → samplingDomain d H), V ∈ 𝓝 P ∧
      ∀ Q ∈ V, scalar Q ≤ (2 * C₃) * I := by
    by_cases hIz : I = 0
    · have huz := continuous_zero_of_integral_sq_zero d H u hu huc hIz
      refine ⟨Set.univ, Filter.univ_mem, ?_⟩
      intro Q _
      simp [scalar, hIz, huz _ (Q _).property]
    · have hIp : 0 < I := lt_of_le_of_ne hI (Ne.symm hIz)
      have hPscalar : scalar P < (2 * C₃) * I := by
        have hh : scalar P ≤ C₃ * I := huP
        nlinarith
      refine ⟨scalar ⁻¹' Iio ((2 * C₃) * I),
        (isOpen_Iio.preimage hscalar).mem_nhds hPscalar, fun Q hQ => hQ.le⟩
  obtain ⟨V, hVP, hVcontrol⟩ := hV
  obtain ⟨Q, hQV, hQinj, hQ⟩ := distinct_sampling_in_neighborhood
    (samplingDomain_infinite_neighborhood d H hd) (sparseDimension_pos d H hd) φ
    (ambientBasis_restricted_continuous d H) a P hC₂ hC₃ hP' V hVP
  refine ⟨m, hDm, hm, hmc', Q, a, ?_, ha, ?_, hVcontrol Q hQV⟩
  · intro j k hjk
    apply hQinj
    exact Subtype.ext hjk
  · intro b
    simpa only [hn b] using hQ b

end Tusnady.SamplingSpace
