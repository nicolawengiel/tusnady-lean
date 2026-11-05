import Tusnady.WalshActivity
import Tusnady.TanhCalculus

/-! Concrete smoothed sign blocks from Main.pdf Lemma 2.3. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual function used by every manuscript block. -/
def smoothedBlock (theta : ℝ) (x : Cube ι) : ℝ :=
  Real.tanh (theta * ∑ i, bitSign (x i))

theorem abs_smoothedBlock_le_one (theta : ℝ) (x : Cube ι) :
    |smoothedBlock theta x| ≤ 1 := abs_tanh_le_one _

theorem smoothedBlock_odd (theta : ℝ) (x : Cube ι) :
    smoothedBlock theta (negateCube x) = -smoothedBlock theta x := by
  simp [smoothedBlock, negateCube, Finset.sum_neg_distrib]

theorem smoothedBlock_even_coefficient (theta : ℝ) (S : Finset ι) (hS : Even S.card) :
    coefficient (smoothedBlock theta) S = 0 :=
  coefficient_even_eq_zero (smoothedBlock_odd theta) S hS

theorem smoothedBlock_permute (theta : ℝ) (e : ι ≃ ι) (x : Cube ι) :
    smoothedBlock theta (permuteCube e x) = smoothedBlock theta x := by
  unfold smoothedBlock
  rw [sign_sum_permute]

/-- All singleton coefficients in a block are equal, exactly as stated
in Lemma 2.3(ii); this does not assert their lower bound yet. -/
theorem smoothedBlock_singleton_coefficient_eq (theta : ℝ) (i j : ι) :
    coefficient (smoothedBlock theta) {i} = coefficient (smoothedBlock theta) {j} := by
  have h := mean_reindex (permuteCube (Equiv.swap i j))
    (fun x => smoothedBlock theta x * character {i} x)
  have hp (x : Cube ι) :
      smoothedBlock theta (permuteCube (Equiv.swap i j) x) *
        character {i} (permuteCube (Equiv.swap i j) x) =
        smoothedBlock theta x * character {j} x := by
    rw [smoothedBlock_permute]
    simp [character, permuteCube]
  simp only [hp] at h
  exact h.symm

/-- Separating one sign from the sum is a proved finite update identity. -/
theorem sum_sign_update (i : ι) (x : Cube ι) (b : Bool) :
    (∑ j, bitSign (Function.update x i b j)) =
      bitSign b + ∑ j ∈ (Finset.univ : Finset ι).erase i, bitSign (x j) := by
  have hf : (fun j => bitSign (Function.update x i b j)) =
      Function.update (fun j => bitSign (x j)) i (bitSign b) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp only [Function.update_of_ne hj]
  rw [hf, Finset.sum_update_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase]

/-- The first finite-difference bound is proved for the concrete block,
using the global Lipschitz estimate of tanh. -/
theorem smoothedBlock_derivative_bound {theta : ℝ} (htheta : 0 ≤ theta)
    (i : ι) (x : Cube ι) : |derivative (smoothedBlock theta) i x| ≤ theta := by
  unfold derivative smoothedBlock
  rw [abs_div]
  have hd : theta * (∑ j, bitSign (Function.update x i true j)) -
      theta * (∑ j, bitSign (Function.update x i false j)) = 2 * theta := by
    rw [sum_sign_update, sum_sign_update]
    norm_num [bitSign]
    ring
  have h := abs_tanh_sub_le
    (theta * ∑ j, bitSign (Function.update x i true j))
    (theta * ∑ j, bitSign (Function.update x i false j))
  calc
    _ ≤ |theta * (∑ j, bitSign (Function.update x i true j)) -
        theta * (∑ j, bitSign (Function.update x i false j))| / |(2 : ℝ)| :=
      div_le_div_of_nonneg_right h (abs_nonneg _)
    _ = theta := by rw [hd]; simp [abs_mul, abs_of_nonneg htheta]

/-- Lemma 2.3(iii), first activity estimate, for the actual tanh block. -/
theorem smoothedBlock_first_activity {theta : ℝ} (htheta : 0 ≤ theta) (E : Finset ι) :
    (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S ⊆ E ∧ S.Nonempty),
      coefficient (smoothedBlock theta) S ^ 2) ≤ theta ^ 2 * (E.card : ℝ) :=
  first_activity_of_derivative_bound _ E htheta
    (fun i _ x => smoothedBlock_derivative_bound htheta i x)

/-- Every coefficient vector in [-1,1] produces a block bounded by one. -/
theorem abs_smoothedBlock_extension_le_one (theta : ℝ) {y : ι → ℝ}
    (hy : ∀ i, |y i| ≤ 1) : |extension (smoothedBlock theta) y| ≤ 1 :=
  abs_extension_le (abs_smoothedBlock_le_one theta) hy

end Tusnady.Walsh
