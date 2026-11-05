import Tusnady.ConcreteResponse
import Tusnady.RemainderConcreteSampling
import Tusnady.RemainderPhysical

/-! Actual expected squared error of the physical sampled response. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace.ConcreteSample
variable {d h m : ℕ} {c L : ℝ}

def sampledRemainder (A : ConcreteSample d h m c L) (j : Fin d) (theta : ℝ)
    (u : Witness.Shell d h → ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun k => Witness.physicalRemainder j theta u (A.nodes k))

lemma sampledRemainder_continuous (A : ConcreteSample d h m c L) (hd : 0 < d)
    (j : Fin d) (theta : ℝ) : Continuous (A.sampledRemainder j theta) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
  apply continuous_pi
  intro k
  have he : (fun u : Witness.Shell d h → ℝ => Witness.physicalRemainder j theta u (A.nodes k)) =
      (fun u : Witness.Shell d h → ℝ => Haar.pointPrimitiveHighCLM d (h + 3 * d) h (A.nodes k)
        (Witness.cubicTestL2 j theta u)) := by
    funext u
    exact (Witness.pointPrimitiveHighCLM_cubic_eq_physical hd j theta u (A.nodes k)
      (samplingDomain_subset_UnitCube (A.nodes k).property)).symm
  rw [he]
  exact (Haar.pointPrimitiveHighCLM d (h + 3 * d) h (A.nodes k)).continuous.comp
    (Witness.continuous_cubicTestL2 j theta)

lemma response_remainder_sq_integrable (A : ConcreteSample d h m c L) (hd : 0 < d)
    (Hhaar : ℕ) (j : Fin d) (theta : ℝ) :
    Integrable (fun u => ‖(A.response Hhaar).adjoint (A.sampledRemainder j theta u)‖ ^ 2)
      (UniformMonomial.cubeLaw (Witness.Shell d h)) := by
  have hc := (A.response Hhaar).adjoint.continuous.comp (A.sampledRemainder_continuous hd j theta)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image hc).isBounded.exists_norm_le
  have hm : MemLp (fun u => (A.response Hhaar).adjoint (A.sampledRemainder j theta u)) 2
      (UniformMonomial.cubeLaw (Witness.Shell d h)) := by
    apply MemLp.of_bound hc.measurable.aestronglyMeasurable B
    filter_upwards [UniformMonomial.ae_cube (Witness.Shell d h)] with u hu
    apply hB
    refine ⟨u, ?_, rfl⟩
    exact ⟨fun i => (abs_le.mp (hu i)).1, fun i => (abs_le.mp (hu i)).2⟩
  exact hm.integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)

theorem expected_response_remainder_sq_le (A : ConcreteSample d h m c L) (hd : 0 < d)
    (Hhaar : ℕ) (j : Fin d) (theta : ℝ) :
    (∫ u, ‖(A.response Hhaar).adjoint (A.sampledRemainder j theta u)‖ ^ 2
      ∂UniformMonomial.cubeLaw (Witness.Shell d h)) ≤
      ((m : ℝ) / L) * ∑ k, A.weights k * Witness.cubicEnergyDensity (h := h) j theta (A.nodes k) := by
  have hP : ∀ k, (A.nodes k : Fin d → ℝ) ∈ UnitCube d :=
    fun k => samplingDomain_subset_UnitCube (A.nodes k).property
  have hi : Integrable (fun u => ((m : ℝ) / L) *
      ∑ k, A.weights k * Witness.physicalRemainder j theta u (A.nodes k) ^ 2)
      (UniformMonomial.cubeLaw (Witness.Shell d h)) :=
    (integrable_finset_sum Finset.univ (fun k _ =>
      (Witness.physical_remainder_sq_integrable hd j theta (A.nodes k) (hP k)).const_mul _)).const_mul _
  have he := integral_mono (A.response_remainder_sq_integrable hd Hhaar j theta) hi
    (fun u => A.response_error_sq_le Hhaar (A.sampledRemainder j theta u))
  rw [integral_const_mul, Witness.expected_weighted_physical_remainder hd j theta
    A.weights (fun k => (A.nodes k : Fin d → ℝ)) hP] at he
  exact he

end Tusnady.SamplingSpace.ConcreteSample

namespace Tusnady.SamplingSpace

theorem remainder_response_construction (hLT : Literature.Sampling) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ d h : ℕ, 0 < d → ∀ (j : Fin d) (theta : ℝ),
        ∃ m : ℕ, sparseDimension d (h + 3 * d) ≤ m ∧
          (m : ℝ) ≤ C₁ * sparseDimension d (h + 3 * d) ∧
          ∃ A : ConcreteSample d h m C₂ (2 * (28 : ℝ) ^ d),
            Function.Injective (fun k => (A.nodes k : Fin d → ℝ)) ∧
            (∫ u, ‖(A.response (h + 3 * d)).adjoint (A.sampledRemainder j theta u)‖ ^ 2
              ∂UniformMonomial.cubeLaw (Witness.Shell d h)) ≤
              ((m : ℝ) * C₃ / (2 * (28 : ℝ) ^ d)) *
                (∫ x, Witness.cubicEnergyDensity (h := h) j theta x ∂Haar.cubeMeasure d) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hs⟩ := remainder_concrete_samples hLT
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro d h hd j theta
  obtain ⟨m, hdm, hmc, A, hinj, ha⟩ := hs d h hd j theta
  refine ⟨m, hdm, hmc, A, hinj, (A.expected_response_remainder_sq_le hd _ j theta).trans ?_⟩
  have he := mul_le_mul_of_nonneg_left ha
    (by positivity : 0 ≤ (m : ℝ) / (2 * (28 : ℝ) ^ d))
  convert he using 1 <;> ring

end Tusnady.SamplingSpace
