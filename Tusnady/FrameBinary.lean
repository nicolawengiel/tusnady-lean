import Tusnady.FrameMSS
import Tusnady.FrameBasic

/-! Actual binary random vectors for the r=2 MSS partition. -/
noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
namespace Tusnady.Frame
open RealRooted.MixedCharacteristic

@[simp] lemma append_addNat_same {D : ℕ} (x y : Fin D → ℝ) (i : Fin D) :
    Fin.append x y (i.addNat D) = y i := by
  rw [← Fin.natAdd_eq_addNat]
  exact Fin.append_right x y i

@[simp] lemma castAdd_ne_addNat_same {D : ℕ} (a b : Fin D) :
    Fin.castAdd D a ≠ b.addNat D := by
  intro h
  have he := congrArg Fin.val h
  change a.val = b.val + D at he
  omega

def block {D : ℕ} (b : Bool) (x : Fin D → ℝ) : Fin (D+D) → ℝ :=
  if b then Fin.append 0 x else Fin.append x 0

def binaryVector {D : ℕ} (x : Fin D → ℝ) (b : Bool) : Fin (D+D) → ℝ :=
  Real.sqrt 2 • block b x

lemma block_sq_sum {D : ℕ} (b : Bool) (x : Fin D → ℝ) :
    ∑ i, (block b x i)^2 = ∑ i, (x i)^2 := by
  cases b <;> simp [block, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

lemma block_dot {D : ℕ} (b c : Bool) (x y : Fin D → ℝ) :
    block b x ⬝ᵥ block c y = if b = c then x ⬝ᵥ y else 0 := by
  cases b <;> cases c <;>
    simp [block, dotProduct, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

lemma binary_dot {D : ℕ} (b c : Bool) (x y : Fin D → ℝ) :
    block b x ⬝ᵥ binaryVector y c =
      if b = c then Real.sqrt 2 * (x ⬝ᵥ y) else 0 := by
  rw [binaryVector, dotProduct_smul, block_dot]
  split_ifs <;> simp

lemma binary_sq_sum {D : ℕ} (x : Fin D → ℝ) (b : Bool) :
    ∑ i, (binaryVector x b i)^2 = 2 * ∑ i, (x i)^2 := by
  simp only [binaryVector, Pi.smul_apply, smul_eq_mul, mul_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), ← Finset.mul_sum, block_sq_sum]

lemma binary_moment_trace {D : ℕ} (x : Fin D → ℝ) :
    (secondMoment (binaryVector x) (fun _ : Bool => (1/2:ℝ))).trace =
      2 * ∑ i, (x i)^2 := by
  rw [Tusnady.FrameMSS.secondMoment_trace]
  simp [binary_sq_sum, Fintype.sum_bool]

lemma binary_moment_left_left {D : ℕ} (x : Fin D → ℝ) (a b : Fin D) :
    secondMoment (binaryVector x) (fun _ : Bool => (1/2:ℝ))
      (Fin.castAdd D a) (Fin.castAdd D b) = x a * x b := by
  simp [secondMoment, Fintype.sum_bool, binaryVector, block, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Fin.append_left, Pi.smul_apply, smul_eq_mul]
  linear_combination (x a * x b / 2) * Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)

lemma binary_moment_right_right {D : ℕ} (x : Fin D → ℝ) (a b : Fin D) :
    secondMoment (binaryVector x) (fun _ : Bool => (1/2:ℝ))
      (Fin.natAdd D a) (Fin.natAdd D b) = x a * x b := by
  simp [secondMoment, Fintype.sum_bool, binaryVector, block, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Fin.append_right, Pi.smul_apply, smul_eq_mul]
  linear_combination (x a * x b / 2) * Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)

lemma binary_moment_left_right {D : ℕ} (x : Fin D → ℝ) (a b : Fin D) :
    secondMoment (binaryVector x) (fun _ : Bool => (1/2:ℝ))
      (Fin.castAdd D a) (Fin.natAdd D b) = 0 := by
  simp [secondMoment, Fintype.sum_bool, binaryVector, block, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Fin.append_left, Fin.append_right,
    Pi.smul_apply, smul_eq_mul]

lemma binary_moment_right_left {D : ℕ} (x : Fin D → ℝ) (a b : Fin D) :
    secondMoment (binaryVector x) (fun _ : Bool => (1/2:ℝ))
      (Fin.natAdd D a) (Fin.castAdd D b) = 0 := by
  simp [secondMoment, Fintype.sum_bool, binaryVector, block, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Fin.append_left, Fin.append_right,
    Pi.smul_apply, smul_eq_mul]

lemma binary_moment_sum {D M : ℕ} (v : Fin M → Space D)
    (hgram : (∑ j, Matrix.vecMulVec (fun i => v j i) (fun i => v j i)) =
      (1 : Matrix (Fin D) (Fin D) ℝ)) :
    (∑ j, secondMoment (binaryVector (fun i => v j i)) (fun _ : Bool => (1/2:ℝ))) =
      (1 : Matrix (Fin (D+D)) (Fin (D+D)) ℝ) := by
  ext a b
  refine Fin.addCases (fun a => ?_) (fun a => ?_) a
  · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · have hij := congrArg (fun A : Matrix (Fin D) (Fin D) ℝ => A a b) hgram
      simpa only [Matrix.sum_apply, binary_moment_left_left, Matrix.vecMulVec_apply,
        Matrix.one_apply, Fin.castAdd_inj] using hij
    · simp only [Matrix.sum_apply, ← Fin.natAdd_eq_addNat, binary_moment_left_right,
        Matrix.one_apply]
      simp
  · refine Fin.addCases (fun b => ?_) (fun b => ?_) b
    · simp only [Matrix.sum_apply, ← Fin.natAdd_eq_addNat, binary_moment_right_left,
        Matrix.one_apply]
      simp [(castAdd_ne_addNat_same b a).symm]
    · have hij := congrArg (fun A : Matrix (Fin D) (Fin D) ℝ => A a b) hgram
      simpa only [Matrix.sum_apply, binary_moment_right_right, Matrix.vecMulVec_apply,
        Matrix.one_apply, Fin.natAdd_inj] using hij

lemma quadratic_sum_outer {n m : ℕ} (v : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((∑ j, Matrix.vecMulVec (v j) (v j)) *ᵥ x) =
      ∑ j, (x ⬝ᵥ v j)^2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro j _
  have heq : Matrix.vecMulVec (v j) (v j) *ᵥ x = (v j ⬝ᵥ x) • v j := by
    ext k
    simp [Matrix.vecMulVec_mulVec, smul_eq_mul, mul_comm]
  rw [heq, dotProduct_smul, dotProduct_comm (v j) x]
  simp only [smul_eq_mul]
  ring

end Tusnady.Frame
