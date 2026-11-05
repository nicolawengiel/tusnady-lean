import Tusnady.SmoothedBlockHigher
import Tusnady.TanhSecant

/-! The exact first Walsh coefficient bounds for the concrete tanh block. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mean_sub (f g : Cube ι → ℝ) : mean (fun x => f x - g x) = mean f - mean g := by
  simp only [mean, Finset.sum_sub_distrib, sub_div]

/-- The second moment of any sum of distinct signs is exactly its size. -/
theorem mean_sign_sum_sq (A : Finset ι) :
    mean (fun x : Cube ι => (∑ j ∈ A, bitSign (x j)) ^ 2) = (A.card : ℝ) := by
  have hv : ∀ j ∈ A, ∀ k ∈ A,
      mean (fun x : Cube ι => bitSign (x j) * bitSign (x k)) = if j = k then 1 else 0 := by
    intro j _ k _
    simpa [character] using character_orthogonality ({j} : Finset ι) {k}
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
    mean_sq_sum_orthonormal A (fun _ => (1 : ℝ)) (fun j x => bitSign (x j)) hv

/-- The exact quantitative lower bound in Main.pdf Lemma 2.3(ii).
The finite average and cubic correction are derived, not postulated. -/
theorem smoothedBlock_singleton_lower {theta : ℝ} (htheta : 0 ≤ theta) (i : ι) :
    theta * (1 - theta ^ 2 * ((Fintype.card ι : ℝ) - (2 : ℝ) / 3)) ≤
      coefficient (smoothedBlock theta) {i} := by
  let A : Finset ι := Finset.univ.erase i
  have hc : 1 ≤ Fintype.card ι := by
    have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    omega
  have hcard : (A.card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    dsimp only [A]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Nat.cast_sub hc]
    norm_num
  have heq (x : Cube ι) :
      theta * (1 - (theta * ∑ j ∈ A, bitSign (x j)) ^ 2 - theta ^ 2 / 3) =
      theta * (1 - theta ^ 2 / 3) - theta ^ 3 * (∑ j ∈ A, bitSign (x j)) ^ 2 := by ring
  have hmean : mean (fun x : Cube ι =>
      theta * (1 - (theta * ∑ j ∈ A, bitSign (x j)) ^ 2 - theta ^ 2 / 3)) =
      theta * (1 - theta ^ 2 * ((Fintype.card ι : ℝ) - (2 : ℝ) / 3)) := by
    simp_rw [heq]
    rw [mean_sub, mean_const, mean_const_mul, mean_sign_sum_sq, hcard]
    ring
  have hpoint (x : Cube ι) :
      theta * (1 - (theta * ∑ j ∈ A, bitSign (x j)) ^ 2 - theta ^ 2 / 3) ≤
      derivative (smoothedBlock theta) i x := by
    change _ ≤ derivative (blockOn Finset.univ Real.tanh theta) i x
    rw [derivative_blockOn _ _ _ (Finset.mem_univ i)]
    exact centralDifference_tanh_lower htheta _
  have h := mean_mono _ _ hpoint
  rwa [hmean, mean_derivative] at h

/-- Upper bound in the same lemma, using the actual finite derivative. -/
theorem smoothedBlock_singleton_upper {theta : ℝ} (htheta : 0 ≤ theta) (i : ι) :
    coefficient (smoothedBlock theta) {i} ≤ theta := by
  rw [← mean_derivative]
  calc
    _ ≤ mean (fun _ : Cube ι => theta) := by
      apply mean_mono
      intro x
      exact (le_abs_self _).trans (smoothedBlock_derivative_bound htheta i x)
    _ = theta := mean_const theta

/-- The complete interval for linear response needed in Main.pdf Lemma 3.3. -/
theorem smoothedBlock_linear_interval {theta : ℝ} (htheta : 0 ≤ theta)
    (hbudget : theta ^ 2 * (Fintype.card ι : ℝ) ≤ (1 : ℝ) / 4) (i : ι) :
    theta / 2 ≤ coefficient (smoothedBlock theta) {i} ∧
      coefficient (smoothedBlock theta) {i} ≤ theta := by
  constructor
  · have h := smoothedBlock_singleton_lower htheta i
    have hsmall := mul_le_mul_of_nonneg_left hbudget htheta
    nlinarith [pow_nonneg htheta 3]
  · exact smoothedBlock_singleton_upper htheta i

end Tusnady.Walsh
