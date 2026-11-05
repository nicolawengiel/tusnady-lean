import Tusnady.ConcreteGram
import Tusnady.LinearPrimitive

/-! Actual physical matrix, row bounds, exact shell response and the
literal sampled linear primitive response of the constructed operator. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.SamplingSpace.ConcreteSample
open GramResponse
variable {d h m : ℕ} {c L : ℝ}

lemma euclidean_sum_apply {ι J : Type*} [Fintype ι] [Fintype J]
    (f : J → EuclideanSpace ℝ ι) (i : ι) : (∑ j, f j) i = ∑ j, f j i :=
  map_sum (PiLp.projₗ (𝕜 := ℝ) (p := 2) (β := fun _ : ι => ℝ) i) _ _

lemma evaluation_shellSynthesis (A : ConcreteSample d h m c L)
    (x : Witness.ShellCoefficients d h) (j : Fin m) :
    A.evaluation (sparseShellSynthesis d h x) j =
      ∑ R, x R * Witness.normalizedPrimitive R (A.nodes j) := by
  classical
  have he : sparseShellSynthesis d h x = ∑ R, x R •
      (⟨Witness.shellPrimitiveVector R, shellPrimitiveVector_mem_sparse R⟩ :
        sparseCubeSpace d (h + 3 * d)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rfl
  rw [he, map_sum]
  simp only [map_smul, euclidean_sum_apply, PiLp.smul_apply, smul_eq_mul, evaluation,
    sparseEvaluation_apply, shellPrimitiveVector_representative]

lemma targetOperator_adjoint (A : ConcreteSample d h m c L) :
    A.targetOperator.adjoint = A.targetOperator := by
  simp [targetOperator]

theorem response_adjoint_shell (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (x : Witness.ShellCoefficients d h) :
    (A.response Hhaar).adjoint (A.evaluation (sparseShellSynthesis d h x)) =
      A.targetScale • x := by
  change _ = A.targetOperator x
  rw [← A.targetOperator_adjoint]
  unfold response sampledWeightedResponse
  exact weightedResponse_adjoint_shell _ _ _ _ _ _ _ x

theorem response_injective (A : ConcreteSample d h m c L) (Hhaar : ℕ) :
    Function.Injective (A.response Hhaar) := by
  intro x y hxy
  have he := congrArg (A.evaluation.comp (sparseShellSynthesis d h)).adjoint hxy
  rw [A.response_exact, A.response_exact] at he
  exact (smul_right_injective (M := Witness.ShellCoefficients d h) A.targetScale_pos.ne') he

theorem response_adjoint_low (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (v : sparseLowPrimitiveSpace d Hhaar h) :
    (A.response Hhaar).adjoint (A.evaluation v) = (0 : Witness.ShellCoefficients d h) := by
  unfold response sampledWeightedResponse
  exact weightedResponse_adjoint_low _ _ _ _ _ _ _ v

theorem response_adjoint_lowTensor (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (T : Haar.TensorLabel d Hhaar) (hT : Haar.tensorLevel T ≤ (h : ℤ) - 1) :
    (A.response Hhaar).adjoint
      (WithLp.toLp 2 (fun j => Haar.normalizedTensorPrimitiveValue T (A.nodes j))) =
      (0 : Witness.ShellCoefficients d h) := by
  classical
  let v : sparseCubeSpace d (h + 3 * d) :=
    ⟨Haar.primitiveCLM d (Haar.tensorL2 T), lowTensorPrimitive_mem_sparse T hT⟩
  have hv : v ∈ sparseLowPrimitiveSpace d Hhaar h := by
    exact ⟨Haar.tensorL2 T, Submodule.subset_span (Finset.mem_image.mpr
      ⟨T, Finset.mem_filter.mpr ⟨Finset.mem_univ T, hT⟩, rfl⟩), rfl⟩
  have he : A.evaluation v = WithLp.toLp 2
      (fun j => Haar.normalizedTensorPrimitiveValue T (A.nodes j)) := by
    ext j
    exact lowTensorPrimitive_representative T hT (A.nodes j) (A.nodes j).property.1
  rw [← he]
  exact A.response_adjoint_low Hhaar ⟨v, hv⟩

def responseMatrix (A : ConcreteSample d h m c L) (Hhaar : ℕ) :
    Matrix (Fin m) (Witness.Shell d h) ℝ :=
  fun j R => A.response Hhaar (EuclideanSpace.single R 1) j

lemma responseMatrix_mulVec (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (x : Witness.ShellCoefficients d h) (j : Fin m) :
    (A.responseMatrix Hhaar).mulVec (fun R => x R) j = A.response Hhaar x j := by
  classical
  have hx : (∑ R, x R • EuclideanSpace.single R 1 : Witness.ShellCoefficients d h) = x := by
    ext R
    simp [euclidean_sum_apply, EuclideanSpace.single_apply]
  nth_rw 2 [← hx]
  rw [map_sum]
  simp only [map_smul, euclidean_sum_apply, PiLp.smul_apply, smul_eq_mul]
  change _ = ∑ R, x R * A.response Hhaar (EuclideanSpace.single R 1) j
  unfold Matrix.mulVec dotProduct responseMatrix
  apply Finset.sum_congr rfl
  intro R _
  ring

lemma responseMatrix_adjoint (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (r : EuclideanSpace ℝ (Fin m)) (R : Witness.Shell d h) :
    (A.response Hhaar).adjoint r R = ∑ j, A.responseMatrix Hhaar j R * r j := by
  calc
    _ = inner ℝ (EuclideanSpace.single R 1) ((A.response Hhaar).adjoint r) := by
      rw [EuclideanSpace.inner_single_left]; simp
    _ = inner ℝ (A.response Hhaar (EuclideanSpace.single R 1)) r :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = _ := by
      rw [PiLp.inner_apply]
      apply Finset.sum_congr rfl
      intro j _
      simp [responseMatrix, RCLike.inner_apply, mul_comm]

theorem responseMatrix_injective (A : ConcreteSample d h m c L) (Hhaar : ℕ) :
    Function.Injective (A.responseMatrix Hhaar).mulVecLin := by
  intro x y hxy
  have he : A.response Hhaar (WithLp.toLp 2 x) = A.response Hhaar (WithLp.toLp 2 y) := by
    ext j
    rw [← responseMatrix_mulVec, ← responseMatrix_mulVec]
    exact congrFun hxy j
  exact congrArg WithLp.ofLp (A.response_injective Hhaar he)

theorem responseMatrix_row_sq_le_one (A : ConcreteSample d h m c L) (Hhaar : ℕ) (j : Fin m) :
    (∑ R, A.responseMatrix Hhaar j R ^ 2) ≤ 1 := by
  have hnorm : ‖(A.response Hhaar).adjoint (EuclideanSpace.single j 1)‖ ≤ 1 := by
    have hop : ‖(A.response Hhaar).adjoint‖ ≤ 1 := by
      simpa using A.response_opNorm_le_one Hhaar
    exact ((A.response Hhaar).adjoint.le_opNorm (EuclideanSpace.single j 1)).trans
      (by simpa using hop)
  have he : (∑ R, A.responseMatrix Hhaar j R ^ 2) =
      ‖(A.response Hhaar).adjoint (EuclideanSpace.single j 1)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro R _
    rw [responseMatrix_adjoint]
    simp [EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]
  rw [he]
  nlinarith [norm_nonneg ((A.response Hhaar).adjoint (EuclideanSpace.single j 1))]

theorem response_linearPrimitive (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (j : Fin d) (theta : ℝ) (u : Witness.Shell d h → ℝ) (R : Witness.Shell d h) :
    (A.response Hhaar).adjoint
      (WithLp.toLp 2 (fun k => Witness.linearPrimitiveValue j theta u (A.nodes k))) R =
      A.targetScale * Witness.shellVolume h * Witness.linearCoefficient j theta R * u R := by
  let x : Witness.ShellCoefficients d h := WithLp.toLp 2 (fun R =>
    Witness.shellVolume h * Witness.linearCoefficient j theta R * u R)
  have he : A.evaluation (sparseShellSynthesis d h x) =
      WithLp.toLp 2 (fun k => Witness.linearPrimitiveValue j theta u (A.nodes k)) := by
    ext k
    rw [evaluation_shellSynthesis]
    change (∑ R, (Witness.shellVolume h * Witness.linearCoefficient j theta R * u R) *
      Witness.normalizedPrimitive R (A.nodes k)) = _
    change (∑ R, (Witness.shellVolume h * Witness.linearCoefficient j theta R * u R) *
      Witness.normalizedPrimitive R (A.nodes k)) = Witness.linearPrimitiveValue j theta u (A.nodes k)
    unfold Witness.linearPrimitiveValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R _
    ring
  rw [← he, response_adjoint_shell]
  change A.targetScale * (Witness.shellVolume h * Witness.linearCoefficient j theta R * u R) = _
  ring

end Tusnady.SamplingSpace.ConcreteSample
