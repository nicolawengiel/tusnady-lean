import Tusnady.FrameBasic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Actual Gram matrices of finite real frames -/

noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
namespace Tusnady.Frame

/-- The actual sum of rank-one coordinate matrices. -/
def gram {D M : ℕ} (v : Fin M → Space D) (S : Finset (Fin M)) :
    Matrix (Fin D) (Fin D) ℝ :=
  ∑ j ∈ S, Matrix.vecMulVec (fun i => v j i) (fun i => v j i)

/-- The tight-frame identity implies the exact matrix identity, by polarization. -/
theorem tight_gram {D M : ℕ} (v : Fin M → Space D) (hv : Tight v) :
    (∑ j, Matrix.vecMulVec (fun i => v j i) (fun i => v j i)) =
      (1 : Matrix (Fin D) (Fin D) ℝ) := by
  classical
  have hdiag (i : Fin D) : ∑ j, (v j i) ^ 2 = 1 := by
    have hh := hv (EuclideanSpace.single i 1)
    simpa [energy, EuclideanSpace.inner_single_left] using hh
  ext i k
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.one_apply]
  by_cases hik : i = k
  · subst k
    simpa only [if_true, ← pow_two] using hdiag i
  · have hsum : ∑ j, (v j i + v j k) ^ 2 = 2 := by
      have hh := hv (EuclideanSpace.single i 1 + EuclideanSpace.single k 1)
      rw [norm_add_sq_real] at hh
      simp [energy, inner_add_left, EuclideanSpace.inner_single_left,
        EuclideanSpace.single_apply, hik] at hh
      norm_num at hh
      exact hh
    have hexpand : (∑ j, (v j i + v j k) ^ 2) =
        (∑ j, (v j i)^2) + 2 * (∑ j, v j i * v j k) + (∑ j, (v j k)^2) := by
      calc
        (∑ j, (v j i + v j k)^2) =
            ∑ j, ((v j i)^2 + 2*(v j i*v j k) + (v j k)^2) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    rw [hdiag i, hdiag k, hsum] at hexpand
    simp only [hik, if_false]
    linarith

/-- A single rank-one matrix gives the square of the genuine frame coefficient. -/
theorem quadratic_vecMulVec {D : ℕ} (a w : Space D) :
    (w : Fin D → ℝ) ⬝ᵥ (Matrix.vecMulVec (fun i => a i) (fun i => a i) *ᵥ
      (w : Fin D → ℝ)) = inner ℝ w a ^ 2 := by
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, PiLp.inner_apply,
    RCLike.inner_apply', conj_trivial]
  change (∑ i, w i * ∑ j, a i * a j * w j) = (∑ i, w i * a i)^2
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual Gram quadratic form equals the actual subset frame energy. -/
theorem quadratic_gram {D M : ℕ} (v : Fin M → Space D) (S : Finset (Fin M))
    (w : Space D) :
    (w : Fin D → ℝ) ⬝ᵥ (gram v S *ᵥ (w : Fin D → ℝ)) = energy v S w := by
  classical
  unfold gram
  rw [Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl (fun j _ => quadratic_vecMulVec (v j) w)

end Tusnady.Frame
