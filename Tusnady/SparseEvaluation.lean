import Tusnady.SparseCubeHilbert
import Tusnady.GramResponse

/-! Genuine finite-dimensional point evaluation and actual diagonal
sampling weights, as continuous maps in the Euclidean norms. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.SamplingSpace

def sparseEvaluationLinear {d H m : ℕ} (P : Fin m → Fin d → ℝ) :
    sparseCubeSpace d H →ₗ[ℝ] EuclideanSpace ℝ (Fin m) where
  toFun v := WithLp.toLp 2 (fun j => sparseCubeRepresentative d H v (P j))
  map_add' v w := by
    ext j
    simp [sparseCubeRepresentative, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c v := by
    ext j
    simp [sparseCubeRepresentative, map_smul, smul_eq_mul, mul_assoc, Finset.mul_sum]

def sparseEvaluation {d H m : ℕ} (P : Fin m → Fin d → ℝ) :
    sparseCubeSpace d H →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (sparseEvaluationLinear (H := H) P).toContinuousLinearMap

@[simp] lemma sparseEvaluation_apply {d H m : ℕ} (P : Fin m → Fin d → ℝ)
    (v : sparseCubeSpace d H) (j : Fin m) :
    sparseEvaluation P v j = sparseCubeRepresentative d H v (P j) := rfl

def samplingWeight (m : ℕ) (a : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  GramResponse.diagonalScale m (fun j => Real.sqrt (a j))

lemma samplingWeight_norm_sq {m : ℕ} (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    (r : EuclideanSpace ℝ (Fin m)) :
    ‖samplingWeight m a r‖ ^ 2 = ∑ j, a j * (r j) ^ 2 := by
  simp only [samplingWeight, EuclideanSpace.norm_sq_eq, GramResponse.diagonalScale_apply,
    Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (ha _)]

lemma samplingWeight_opNorm_le {m : ℕ} (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
    {L : ℝ} (hL : 0 ≤ L) (hbound : ∀ j, a j ≤ L) :
    ‖samplingWeight m a‖ ≤ Real.sqrt L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  have hsq : ‖samplingWeight m a x‖ ^ 2 ≤ L * ‖x‖ ^ 2 := by
    exact GramResponse.diagonalScale_norm_sq_le m _ L
      (fun j => by rw [Real.sq_sqrt (ha j)]; exact hbound j) x
  have hs : (Real.sqrt L * ‖x‖) ^ 2 = L * ‖x‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hL]
  exact (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp (hsq.trans_eq hs.symm)

lemma sparseEvaluation_sampling_lower {d H m : ℕ} (P : Fin m → Fin d → ℝ)
    (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (c : ℝ)
    (hsample : ∀ b : Fin (sparseDimension d H) → ℝ,
      c * (∑ i, b i ^ 2) ≤ ∑ j, a j * (∑ i, b i * ambientBasis d H i (P j)) ^ 2)
    (v : sparseCubeSpace d H) :
    c * ‖v‖ ^ 2 ≤ ‖samplingWeight m a (sparseEvaluation P v)‖ ^ 2 := by
  rw [samplingWeight_norm_sq a ha]
  have hs := hsample (sparseCubeCoordinates d H v)
  have hn : (∑ i, sparseCubeCoordinates d H v i ^ 2) = ‖v‖ ^ 2 := by
    rw [← sparseCubeCoordinates_norm_sq d H v]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (EuclideanSpace.norm_sq_eq (sparseCubeCoordinates d H v)).symm
  simpa only [hn] using hs

end Tusnady.SamplingSpace
