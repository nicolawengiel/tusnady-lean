import Tusnady.SparseCubeHilbert
import Tusnady.ShellHilbert

/-! Actual shell and low primitive vectors belong to the finite sparse
Hilbert space; its canonical representatives equal their actual functions. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

lemma shellPrimitiveVector_mem_sparse {d h : ℕ} (R : Witness.Shell d h) :
    Witness.shellPrimitiveVector R ∈ sparseCubeSpace d (h + 3 * d) := by
  obtain ⟨a, ha⟩ := normalizedPrimitive_sampling_coefficients R
  apply mem_sparseCubeSpace_of_coefficients _ _ _ a
  exact (Witness.shellPrimitiveVector_ae R).trans (Filter.Eventually.of_forall ha)

lemma shellPrimitiveVector_representative {d h : ℕ} (R : Witness.Shell d h) (x : Fin d → ℝ) :
    sparseCubeRepresentative d (h + 3 * d) ⟨Witness.shellPrimitiveVector R,
      shellPrimitiveVector_mem_sparse R⟩ x = Witness.normalizedPrimitive R x := by
  obtain ⟨a, ha⟩ := normalizedPrimitive_sampling_coefficients R
  rw [sparseCubeRepresentative_eq_coefficients _ _ _ a
    ((Witness.shellPrimitiveVector_ae R).trans (Filter.Eventually.of_forall ha)) x]
  exact (ha x).symm

lemma lowTensorPrimitive_mem_sparse {d H h : ℕ} (L : Haar.TensorLabel d H)
    (hL : Haar.tensorLevel L ≤ (h : ℤ) - 1) :
    Haar.primitiveCLM d (Haar.tensorL2 L) ∈ sparseCubeSpace d (h + 3 * d) := by
  obtain ⟨a, ha⟩ := lowPrimitive_sampling_coefficients L hL
  apply mem_sparseCubeSpace_of_coefficients _ _ _ a
  filter_upwards [Witness.primitiveCLM_tensorL2_ae L, Haar.cubeMeasure_ae_unit d] with x hx hxu
  exact hx.trans (ha x hxu)

lemma lowTensorPrimitive_representative {d H h : ℕ} (L : Haar.TensorLabel d H)
    (hL : Haar.tensorLevel L ≤ (h : ℤ) - 1) (x : Fin d → ℝ) (hx : x ∈ unitCube d) :
    sparseCubeRepresentative d (h + 3 * d) ⟨Haar.primitiveCLM d (Haar.tensorL2 L),
      lowTensorPrimitive_mem_sparse L hL⟩ x = Haar.normalizedTensorPrimitiveValue L x := by
  obtain ⟨a, ha⟩ := lowPrimitive_sampling_coefficients L hL
  have hae : Haar.primitiveCLM d (Haar.tensorL2 L) =ᵐ[Haar.cubeMeasure d]
      (fun x => ∑ i, a i * ambientBasis d (h + 3 * d) i x) := by
    filter_upwards [Witness.primitiveCLM_tensorL2_ae L, Haar.cubeMeasure_ae_unit d] with x hx hxu
    exact hx.trans (ha x hxu)
  rw [sparseCubeRepresentative_eq_coefficients _ _ _ a hae x]
  exact (ha x hx).symm

theorem lowPrimitiveSpace_le_sparse (d H h : ℕ) :
    Witness.lowPrimitiveSpace d H h ≤ sparseCubeSpace d (h + 3 * d) := by
  classical
  rw [Witness.lowPrimitiveSpace_eq_span]
  apply Submodule.span_le.mpr
  intro f hf
  obtain ⟨L, hL, rfl⟩ := hf
  exact lowTensorPrimitive_mem_sparse L (Finset.mem_filter.mp hL).2

def sparseShellSynthesis (d h : ℕ) :
    Witness.ShellCoefficients d h →L[ℝ] sparseCubeSpace d (h + 3 * d) :=
  (Witness.shellSynthesis d h).codRestrict _ (fun _x =>
    Submodule.sum_mem _ fun R _ => Submodule.smul_mem _ _ (shellPrimitiveVector_mem_sparse R))

def sparseLowPrimitiveSpace (d H h : ℕ) : Submodule ℝ (sparseCubeSpace d (h + 3 * d)) :=
  (Witness.lowPrimitiveSpace d H h).comap (sparseCubeSpace d (h + 3 * d)).subtype

lemma sparseShellSynthesis_norm_sq (d h : ℕ) (x : Witness.ShellCoefficients d h) :
    ‖sparseShellSynthesis d h x‖ ^ 2 = Witness.gamma d * Witness.shellVolume h * ‖x‖ ^ 2 :=
  Witness.shellSynthesis_norm_sq x

lemma sparseShellSynthesis_orthogonal (d H h : ℕ) (x : Witness.ShellCoefficients d h) :
    sparseShellSynthesis d h x ∈ (sparseLowPrimitiveSpace d H h)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro v hv
  have hh := Witness.shellSynthesis_mem_orthogonal (H := H) x
  rw [Submodule.mem_orthogonal'] at hh
  exact hh v hv

end Tusnady.SamplingSpace
