import Tusnady.FrameBasic
import Mathlib.Analysis.Matrix.Spectrum

/-! # Characteristic-root bounds imply actual Euclidean quadratic bounds

This uses the proved orthonormal eigenbasis of a real Hermitian matrix.
No matrix norm, frame-partition premise or spectral estimate is assumed.
-/

noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
namespace Tusnady.Frame

/-- Every eigenvalue is an actual characteristic root, hence obeys the given bound. -/
theorem eigenvalues_le_of_charpoly_roots {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (R : ℝ)
    (hroots : ∀ r ∈ A.charpoly.roots, r ≤ R) (i : Fin n) : hA.eigenvalues i ≤ R := by
  apply hroots
  rw [hA.roots_charpoly_eq_eigenvalues]
  apply Multiset.mem_map.mpr
  exact ⟨i, Finset.mem_val.mpr (Finset.mem_univ _), by simp⟩

/-- Root control bounds the actual Hilbert-space quadratic form. -/
theorem inner_toEuclideanLin_le_of_charpoly_roots {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (R : ℝ)
    (hroots : ∀ r ∈ A.charpoly.roots, r ≤ R) (x : Space n) :
    inner ℝ x (A.toEuclideanLin x) ≤ R * ‖x‖ ^ 2 := by
  let b := hA.eigenvectorBasis
  have heigen (i : Fin n) : A.toEuclideanLin (b i) = hA.eigenvalues i • b i := by
    apply PiLp.ext
    intro j
    simpa only [Matrix.toLpLin_apply, PiLp.smul_apply, Pi.smul_apply, smul_eq_mul] using
      congrFun (hA.mulVec_eigenvectorBasis i) j
  calc
    inner ℝ x (A.toEuclideanLin x) =
        inner ℝ x (A.toEuclideanLin (∑ i, inner ℝ (b i) x • b i)) := by
      rw [b.sum_repr']
    _ = ∑ i, hA.eigenvalues i * inner ℝ (b i) x ^ 2 := by
      rw [map_sum, inner_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, heigen, inner_smul_right, inner_smul_right, real_inner_comm x (b i)]
      ring
    _ ≤ ∑ i, R * inner ℝ (b i) x ^ 2 := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (eigenvalues_le_of_charpoly_roots hA R hroots i) (sq_nonneg _)
    _ = R * ‖x‖ ^ 2 := by rw [← Finset.mul_sum, b.sum_sq_inner_right]

/-- Root control bounds the actual matrix quadratic form on ordinary coordinate functions. -/
theorem dotProduct_mulVec_le_of_charpoly_roots {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (R : ℝ)
    (hroots : ∀ r ∈ A.charpoly.roots, r ≤ R) (x : Fin n → ℝ) :
    x ⬝ᵥ (A *ᵥ x) ≤ R * ∑ i, (x i) ^ 2 := by
  have hh := inner_toEuclideanLin_le_of_charpoly_roots hA R hroots (WithLp.toLp 2 x)
  rw [real_inner_comm] at hh
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    Matrix.toLpLin_apply, WithLp.ofLp_toLp, EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs] using hh

/-- The coordinate quadratic form with the genuine Euclidean norm on its input. -/
theorem dotProduct_mulVec_le_norm_of_charpoly_roots {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (R : ℝ)
    (hroots : ∀ r ∈ A.charpoly.roots, r ≤ R) (x : Space n) :
    (x : Fin n → ℝ) ⬝ᵥ (A *ᵥ (x : Fin n → ℝ)) ≤ R * ‖x‖ ^ 2 := by
  have hh := inner_toEuclideanLin_le_of_charpoly_roots hA R hroots x
  rw [real_inner_comm] at hh
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    Matrix.toLpLin_apply, WithLp.ofLp_toLp] using hh

end Tusnady.Frame
