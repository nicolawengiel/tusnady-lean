import Tusnady.SparseCubeMembers
import Tusnady.SparseEvaluation

/-! The actual weighted Gram response from genuine nodes and weights.
All shell norms, sparse inclusions and low orthogonality are discharged by
proved concrete functions. Local sampling data will be constructed from
the named literature sampling theorem. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.SamplingSpace
open GramResponse

structure ConcreteSample (d h m : ℕ) (c L : ℝ) where
  nodes : Fin m → samplingDomain d (h + 3 * d)
  weights : Fin m → ℝ
  count_pos : 0 < m
  lower_pos : 0 < c
  bound_pos : 0 < L
  weight_nonneg : ∀ j, 0 ≤ weights j
  weight_upper : ∀ j, weights j ≤ L / m
  sampling_lower : ∀ b : Fin (sparseDimension d (h + 3 * d)) → ℝ,
    c * (∑ i, b i ^ 2) ≤ ∑ j, weights j * (∑ i, b i * ambientBasis d (h + 3 * d) i (nodes j)) ^ 2

namespace ConcreteSample
variable {d h m : ℕ} {c L : ℝ}

def evaluation (A : ConcreteSample d h m c L) :=
  sparseEvaluation (H := h + 3 * d) (fun j => (A.nodes j : Fin d → ℝ))

def outerWeight (A : ConcreteSample d h m c L) := samplingWeight m A.weights

lemma actual_sampling_lower (A : ConcreteSample d h m c L) (v : sparseCubeSpace d (h + 3 * d)) :
    c * ‖v‖ ^ 2 ≤ ‖A.outerWeight (A.evaluation v)‖ ^ 2 :=
  sparseEvaluation_sampling_lower _ _ A.weight_nonneg c A.sampling_lower v

lemma shell_scale_pos (d h : ℕ) : 0 < Witness.gamma d * Witness.shellVolume h :=
  mul_pos (Witness.gamma_pos d) (Witness.shellVolume_pos h)

def targetScale (A : ConcreteSample d h m c L) : ℝ :=
  Real.sqrt ((Witness.gamma d * Witness.shellVolume h * c) * ((m : ℝ) / L))

lemma targetScale_pos (A : ConcreteSample d h m c L) : 0 < A.targetScale := by
  apply Real.sqrt_pos.mpr
  have hm : (0 : ℝ) < m := by exact_mod_cast A.count_pos
  exact mul_pos (mul_pos (shell_scale_pos d h) A.lower_pos) (div_pos hm A.bound_pos)

lemma targetScale_sq (A : ConcreteSample d h m c L) :
    A.targetScale ^ 2 = (Witness.gamma d * Witness.shellVolume h * c) * ((m : ℝ) / L) :=
by
  apply Real.sq_sqrt
  have hm : (0 : ℝ) < m := by exact_mod_cast A.count_pos
  exact (mul_pos (mul_pos (shell_scale_pos d h) A.lower_pos) (div_pos hm A.bound_pos)).le

def targetOperator (A : ConcreteSample d h m c L) :
    Witness.ShellCoefficients d h →L[ℝ] Witness.ShellCoefficients d h :=
  A.targetScale • ContinuousLinearMap.id ℝ _

lemma targetOperator_norm_le (A : ConcreteSample d h m c L) :
    ‖A.targetOperator‖ ≤ A.targetScale := by
  apply ContinuousLinearMap.opNorm_le_bound _ A.targetScale_pos.le
  intro x
  simp only [targetOperator, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos A.targetScale_pos]
  exact le_rfl

def response (A : ConcreteSample d h m c L) (Hhaar : ℕ) :
    Witness.ShellCoefficients d h →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  sampledWeightedResponse (sparseLowPrimitiveSpace d Hhaar h) A.evaluation A.outerWeight
    (sparseShellSynthesis d h) (Witness.gamma d * Witness.shellVolume h) c
    (shell_scale_pos d h) A.lower_pos
    (fun x => (sparseShellSynthesis_norm_sq d h x).ge)
    (sparseShellSynthesis_orthogonal d Hhaar h) A.actual_sampling_lower A.targetOperator

theorem response_exact (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (x : Witness.ShellCoefficients d h) :
    (A.evaluation.comp (sparseShellSynthesis d h)).adjoint (A.response Hhaar x) =
      A.targetScale • x :=
  sampledWeightedResponse_exact _ _ _ _ _ _ _ _ _ _ _ _ x

theorem response_low_zero (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (x : Witness.ShellCoefficients d h) :
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (A.evaluation.comp (sparseLowPrimitiveSpace d Hhaar h).subtypeL))
      (A.response Hhaar x) = (0 : sparseLowPrimitiveSpace d Hhaar h) :=
  sampledWeightedResponse_low_zero _ _ _ _ _ _ _ _ _ _ _ _ x

theorem response_error_le (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (r : EuclideanSpace ℝ (Fin m)) :
    ‖(A.response Hhaar).adjoint r‖ ≤
      (A.targetScale / Real.sqrt (Witness.gamma d * Witness.shellVolume h * c)) *
        Real.sqrt (∑ j, A.weights j * (r j) ^ 2) := by
  have he := sampledWeightedResponse_error_le (sparseLowPrimitiveSpace d Hhaar h)
    A.evaluation A.outerWeight (sparseShellSynthesis d h) _ _
    (shell_scale_pos d h) A.lower_pos
    (fun x => (sparseShellSynthesis_norm_sq d h x).ge)
    (sparseShellSynthesis_orthogonal d Hhaar h) A.actual_sampling_lower A.targetOperator r
  have hw : ‖A.outerWeight r‖ = Real.sqrt (∑ j, A.weights j * (r j) ^ 2) := by
    change ‖samplingWeight m A.weights r‖ = _
    rw [← samplingWeight_norm_sq A.weights A.weight_nonneg, Real.sqrt_sq (norm_nonneg _)]
  rw [hw] at he
  exact he.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right A.targetOperator_norm_le (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

lemma outerWeight_opNorm_le (A : ConcreteSample d h m c L) :
    ‖A.outerWeight‖ ≤ Real.sqrt (L / m) :=
  samplingWeight_opNorm_le A.weights A.weight_nonneg (div_nonneg A.bound_pos.le
    (by exact_mod_cast A.count_pos.le)) A.weight_upper

lemma physical_scale_le_one (A : ConcreteSample d h m c L) :
    ‖A.outerWeight‖ * (‖A.targetOperator‖ /
      Real.sqrt (Witness.gamma d * Witness.shellVolume h * c)) ≤ 1 := by
  let q := Witness.gamma d * Witness.shellVolume h * c
  have hq : 0 < q := mul_pos (shell_scale_pos d h) A.lower_pos
  have hm : (0 : ℝ) < m := by exact_mod_cast A.count_pos
  have hfrac : (Real.sqrt (L / m) * (A.targetScale / Real.sqrt q)) ^ 2 = 1 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (div_pos A.bound_pos hm).le, Real.sq_sqrt hq.le,
      A.targetScale_sq]
    dsimp [q]
    field_simp [ne_of_gt (Witness.gamma_pos d), ne_of_gt (Witness.shellVolume_pos h),
      A.lower_pos.ne', A.bound_pos.ne', hm.ne']
  have hn : 0 ≤ Real.sqrt (L / m) * (A.targetScale / Real.sqrt q) :=
    mul_nonneg (Real.sqrt_nonneg _) (div_nonneg A.targetScale_pos.le (Real.sqrt_nonneg _))
  have hp : Real.sqrt (L / m) * (A.targetScale / Real.sqrt q) ≤ 1 := by nlinarith
  calc
    _ ≤ Real.sqrt (L / m) * (A.targetScale / Real.sqrt q) := by
      apply mul_le_mul A.outerWeight_opNorm_le
        (div_le_div_of_nonneg_right A.targetOperator_norm_le (Real.sqrt_nonneg _))
        (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ ≤ 1 := hp

theorem response_opNorm_le_one (A : ConcreteSample d h m c L) (Hhaar : ℕ) :
    ‖A.response Hhaar‖ ≤ 1 := by
  exact (sampledWeightedResponse_opNorm_le (sparseLowPrimitiveSpace d Hhaar h)
    A.evaluation A.outerWeight (sparseShellSynthesis d h) _ _
    (shell_scale_pos d h) A.lower_pos
    (fun x => (sparseShellSynthesis_norm_sq d h x).ge)
    (sparseShellSynthesis_orthogonal d Hhaar h) A.actual_sampling_lower A.targetOperator).trans
      A.physical_scale_le_one

theorem response_contraction (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (x : Witness.ShellCoefficients d h) : ‖A.response Hhaar x‖ ≤ ‖x‖ :=
  ((A.response Hhaar).le_opNorm x).trans
    (mul_le_of_le_one_left (norm_nonneg _) (A.response_opNorm_le_one Hhaar))

theorem response_error_sq_le (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (r : EuclideanSpace ℝ (Fin m)) :
    ‖(A.response Hhaar).adjoint r‖ ^ 2 ≤
      ((m : ℝ) / L) * ∑ j, A.weights j * (r j) ^ 2 := by
  let q := Witness.gamma d * Witness.shellVolume h * c
  have hq : 0 < q := mul_pos (shell_scale_pos d h) A.lower_pos
  have hw : 0 ≤ ∑ j, A.weights j * (r j) ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (A.weight_nonneg j) (sq_nonneg _)
  have he := A.response_error_le Hhaar r
  have he2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg
    (div_nonneg A.targetScale_pos.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))).mpr he
  rw [mul_pow, div_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hw] at he2
  have hr : A.targetScale ^ 2 / q = (m : ℝ) / L := by
    rw [A.targetScale_sq]
    change (q * ((m : ℝ) / L)) / q = _
    field_simp
  rw [hr] at he2
  exact he2

end ConcreteSample
end Tusnady.SamplingSpace
