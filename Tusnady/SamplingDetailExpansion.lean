import Tusnady.SamplingSpaceEvaluation

/-! Canonical pointwise expansion of every V_j function in actual detail
modes of levels at most j. No arbitrary L² representatives are evaluated. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.SamplingSpace

def canonicalRepresentativeLinear (j : ℕ) : l2Space j →ₗ[ℝ] (ℝ → ℝ) where
  toFun := canonicalRepresentative j
  map_add' v w := by
    funext t
    simp only [Pi.add_apply]
    rw [← evaluationKernel_pairing, ← evaluationKernel_pairing, ← evaluationKernel_pairing]
    exact inner_add_right _ _ _
  map_smul' c v := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [← evaluationKernel_pairing, ← evaluationKernel_pairing]
    simp [inner_smul_right]

def detailRepresentativeLinear (j : ℕ) : detailSpace j →ₗ[ℝ] (ℝ → ℝ) :=
  (canonicalRepresentativeLinear j).comp (Submodule.inclusion (detailSpace_le_level j))

def detailPointwiseSpace (j : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (Set.range (detailBasis j))

lemma detailRepresentative_mem (j : ℕ) (v : detailSpace j) :
    detailRepresentative j v ∈ detailPointwiseSpace j := by
  classical
  have he := congrArg (detailRepresentativeLinear j)
    ((stdOrthonormalBasis ℝ (detailSpace j)).sum_repr v)
  rw [map_sum] at he
  simp only [map_smul] at he
  change (∑ i, (stdOrthonormalBasis ℝ (detailSpace j)).repr v i • detailBasis j i) =
    detailRepresentative j v at he
  rw [← he]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, rfl⟩)

abbrev BoundedDetailIndex (j : ℕ) := Σ r : Fin (j + 1), Fin (Module.finrank ℝ (detailSpace r.val))

def boundedDetailBasis (j : ℕ) (i : BoundedDetailIndex j) : ℝ → ℝ := detailBasis i.1.val i.2

def boundedDetailSpace (j : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  Submodule.span ℝ (Set.range (boundedDetailBasis j))

lemma detailPointwiseSpace_le_bounded {r j : ℕ} (hr : r ≤ j) :
    detailPointwiseSpace r ≤ boundedDetailSpace j := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨⟨⟨r, by omega⟩, i⟩, rfl⟩

lemma boundedDetailSpace_mono {j k : ℕ} (hjk : j ≤ k) :
    boundedDetailSpace j ≤ boundedDetailSpace k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact detailPointwiseSpace_le_bounded (by omega : i.1.val ≤ k)
    (Submodule.subset_span ⟨i.2, rfl⟩)

theorem canonicalRepresentative_mem_bounded (j : ℕ) (v : l2Space j) :
    canonicalRepresentative j v ∈ boundedDetailSpace j := by
  induction j with
  | zero =>
    exact detailPointwiseSpace_le_bounded le_rfl (detailRepresentative_mem 0 v)
  | succ j ih =>
    have hv : (v : L2Real) ∈ l2Space j ⊔ detailSpace (j + 1) := by
      rw [l2Space_step_decomposition]
      exact v.property
    obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp hv
    let wj : l2Space j := ⟨w, hw⟩
    let wf : l2Space (j + 1) := ⟨w, l2Space_mono (Nat.le_succ j) hw⟩
    let zd : detailSpace (j + 1) := ⟨z, hz⟩
    let zf : l2Space (j + 1) := ⟨z, detailSpace_le_level (j + 1) hz⟩
    have he : v = wf + zf := Subtype.ext hwz.symm
    have hwrep : canonicalRepresentative (j + 1) wf = canonicalRepresentative j wj :=
      (canonicalRepresentative_nested (Nat.le_succ j) wj).symm
    rw [he, ← show (canonicalRepresentativeLinear (j + 1)) (wf + zf) =
      canonicalRepresentative (j + 1) (wf + zf) from rfl, map_add]
    change canonicalRepresentative (j + 1) wf + canonicalRepresentative (j + 1) zf ∈ _
    rw [hwrep]
    exact (boundedDetailSpace (j + 1)).add_mem
      (boundedDetailSpace_mono (Nat.le_succ j) (ih wj))
      (detailPointwiseSpace_le_bounded le_rfl (detailRepresentative_mem (j + 1) zd))

theorem pointwiseSpace_le_bounded (j : ℕ) : pointwiseSpace j ≤ boundedDetailSpace j := by
  intro f hf
  obtain ⟨a, rfl⟩ := hf
  let v : l2Space j := ⟨l2Synthesis j a, by rw [l2Space_eq_range]; exact ⟨a, rfl⟩⟩
  have he : pointwiseSynthesis j a = canonicalRepresentative j v :=
    canonicalRepresentative_unique j v _ (pointwiseSynthesis_piecewiseAffine j a)
      (l2Synthesis_ae j a)
  rw [he]
  exact canonicalRepresentative_mem_bounded j v

end Tusnady.SamplingSpace
