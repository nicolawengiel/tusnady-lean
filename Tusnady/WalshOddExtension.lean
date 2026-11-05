import Tusnady.Walsh

/-! Oddness of the actual multilinear Walsh extension. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem extension_neg_of_odd {F : Cube ι → ℝ}
    (hodd : ∀ x, F (negateCube x) = -F x) (y : ι → ℝ) :
    extension F (fun i => -y i) = -extension F y := by
  unfold extension
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_neg]
  by_cases hS : Odd S.card
  · rw [hS.neg_one_pow]
    ring
  · have heven := Nat.not_odd_iff_even.mp hS
    rw [coefficient_even_eq_zero hodd S heven]
    ring

theorem extension_sign_of_odd {F : Cube ι → ℝ}
    (hodd : ∀ x, F (negateCube x) = -F x) (y : ι → ℝ)
    (q : ℝ) (hq : |q| = 1) :
    extension F (fun i => q * y i) = q * extension F y := by
  have hq' : q = 1 ∨ q = -1 := (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hq
  rcases hq' with rfl | rfl
  · simp
  · simpa using extension_neg_of_odd hodd y

end Tusnady.Walsh
