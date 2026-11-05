import Tusnady.FrameBinary
import Tusnady.FrameSpectralBound

/-! # Actual binary MSS roots imply the two frame-energy upper bounds -/

noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
namespace Tusnady.Frame
open RealRooted.MixedCharacteristic

/-- A finite sum of genuine real rank-one outer products is PSD. -/
theorem sum_outer_posSemidef {n m : ℕ} (v : Fin m → Fin n → ℝ) :
    (∑ j, Matrix.vecMulVec (v j) (v j)).PosSemidef := by
  have hh := FrameMSS.secondMoment_posSemidef v (fun _ => (1 : ℝ)) (fun _ => by norm_num)
  simpa only [secondMoment, one_smul] using hh

/-- The block quadratic form is exactly twice the corresponding actual frame energy. -/
theorem binary_quadratic_energy {D M : ℕ} (v : Fin M → Space D)
    (s : Fin M → Bool) (b : Bool) (w : Space D) :
    (∑ j, (block b (fun i => w i) ⬝ᵥ binaryVector (fun i => v j i) (s j)) ^ 2) =
      2 * energy v (Finset.univ.filter (fun j => s j = b)) w := by
  classical
  have hdot (j : Fin M) :
      (fun i => w i) ⬝ᵥ (fun i => v j i) = inner ℝ w (v j) := by
    simp only [dotProduct, PiLp.inner_apply, RCLike.inner_apply', conj_trivial]
  unfold energy
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [binary_dot]
  by_cases hj : s j = b
  · simp only [hj, if_true, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hdot]
  · have hbj : b ≠ s j := Ne.symm hj
    simp [hj, hbj]

/-- The true selected matrix root bound controls each binary frame part. -/
theorem binary_energy_bound {D M : ℕ} (v : Fin M → Space D) (s : Fin M → Bool)
    (R : ℝ)
    (hroots : ∀ r ∈ (∑ j, Matrix.vecMulVec (binaryVector (fun i => v j i) (s j))
      (binaryVector (fun i => v j i) (s j))).charpoly.roots, r ≤ R)
    (b : Bool) (w : Space D) :
    2 * energy v (Finset.univ.filter (fun j => s j = b)) w ≤ R * ‖w‖ ^ 2 := by
  have hA := sum_outer_posSemidef (fun j => binaryVector (fun i => v j i) (s j))
  have hh := dotProduct_mulVec_le_of_charpoly_roots hA.isHermitian R hroots
    (block b (fun i => w i))
  rw [quadratic_sum_outer, binary_quadratic_energy, block_sq_sum] at hh
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using hh

end Tusnady.Frame
