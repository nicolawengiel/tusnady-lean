import Tusnady.BlockPolynomial
import Tusnady.SmoothedBlockHigher
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Finite nonnegative block-activity tails

The cubic exponential bound in Main.pdf §4.3 is proved by finite subset
recursion. No elementary-symmetric estimate is assumed.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.RemainderActivity
attribute [local instance] Classical.propDecidable

def tail {A : Type*} (a : A → ℝ) (s : Finset A) (k : ℕ) : ℝ :=
  ∑ T ∈ s.powerset, if k ≤ T.card then ∏ i ∈ T, a i else 0

theorem tail_nonneg {A : Type*} (a : A → ℝ) (s : Finset A) (k : ℕ)
    (ha : ∀ i ∈ s, 0 ≤ a i) : 0 ≤ tail a s k := by
  apply Finset.sum_nonneg
  intro T hT
  split_ifs
  · exact Finset.prod_nonneg (fun i hi => ha i (Finset.mem_powerset.mp hT hi))
  · rfl

theorem tail_insert_zero {A : Type*} [DecidableEq A] (a : A → ℝ)
    (s : Finset A) (i : A) (hi : i ∉ s) :
    tail a (insert i s) 0 = (1 + a i) * tail a s 0 := by
  unfold tail
  simp only [Nat.zero_le, if_true]
  rw [Finset.sum_powerset_insert hi]
  have heq (T : Finset A) (hT : T ∈ s.powerset) :
      (∏ j ∈ insert i T, a j) = a i * ∏ j ∈ T, a j :=
    Finset.prod_insert (fun hj => hi (Finset.mem_powerset.mp hT hj))
  rw [Finset.sum_congr rfl heq, ← Finset.mul_sum]
  ring

theorem tail_insert_succ {A : Type*} [DecidableEq A] (a : A → ℝ)
    (s : Finset A) (i : A) (hi : i ∉ s) (k : ℕ) :
    tail a (insert i s) (k + 1) = tail a s (k + 1) + a i * tail a s k := by
  unfold tail
  rw [Finset.sum_powerset_insert hi]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  have hiT : i ∉ T := fun h => hi (Finset.mem_powerset.mp hT h)
  simp only [Finset.card_insert_of_notMem hiT, Nat.add_le_add_iff_right,
    Finset.prod_insert hiT]
  split_ifs <;> ring

/-- The exact finite cubic exponential estimate used for class II. -/
theorem tail_bounds {A : Type*} [DecidableEq A] (a : A → ℝ) (s : Finset A)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    let z := ∑ i ∈ s, a i
    tail a s 0 ≤ Real.exp z ∧
    tail a s 1 ≤ z * Real.exp z ∧
    tail a s 2 ≤ z ^ 2 / 2 * Real.exp z ∧
    tail a s 3 ≤ z ^ 3 / 6 * Real.exp z := by
  induction s using Finset.induction_on with
  | empty => norm_num [tail]
  | @insert i s hi ih =>
    have hai : 0 ≤ a i := ha i (Finset.mem_insert_self _ _)
    have has : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨h0, h1, h2, h3⟩ := ih has
    let z := ∑ j ∈ s, a j
    have hz : 0 ≤ z := Finset.sum_nonneg has
    have he : Real.exp z ≤ Real.exp (z + a i) := Real.exp_le_exp.mpr (by linarith)
    have hsum : (∑ j ∈ insert i s, a j) = z + a i := by rw [Finset.sum_insert hi]; ring
    dsimp only
    rw [hsum]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [tail_insert_zero a s i hi]
      calc
        _ ≤ (1 + a i) * Real.exp z := mul_le_mul_of_nonneg_left h0 (by linarith)
        _ ≤ Real.exp (a i) * Real.exp z :=
          mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (a i)]) (Real.exp_nonneg z)
        _ = Real.exp (z + a i) := by rw [← Real.exp_add]; congr 1; ring
    · rw [show 1 = 0 + 1 from rfl, tail_insert_succ a s i hi 0]
      calc
        _ ≤ z * Real.exp z + a i * Real.exp z :=
          add_le_add h1 (mul_le_mul_of_nonneg_left h0 hai)
        _ = (z + a i) * Real.exp z := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left he (add_nonneg hz hai)
    · rw [show 2 = 1 + 1 from rfl, tail_insert_succ a s i hi 1]
      calc
        _ ≤ z ^ 2 / 2 * Real.exp z + a i * (z * Real.exp z) :=
          add_le_add h2 (mul_le_mul_of_nonneg_left h1 hai)
        _ = (z ^ 2 / 2 + a i * z) * Real.exp z := by ring
        _ ≤ (z + a i) ^ 2 / 2 * Real.exp z := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg z)
          nlinarith [sq_nonneg (a i)]
        _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)
    · rw [show 3 = 2 + 1 from rfl, tail_insert_succ a s i hi 2]
      calc
        _ ≤ z ^ 3 / 6 * Real.exp z + a i * (z ^ 2 / 2 * Real.exp z) :=
          add_le_add h3 (mul_le_mul_of_nonneg_left h2 hai)
        _ = (z ^ 3 / 6 + a i * z ^ 2 / 2) * Real.exp z := by ring
        _ ≤ (z + a i) ^ 3 / 6 * Real.exp z := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg z)
          nlinarith [mul_nonneg hz (sq_nonneg (a i)), pow_nonneg hai 3]
        _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

theorem tail_three_le {A : Type*} [DecidableEq A] (a : A → ℝ) (s : Finset A)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    tail a s 3 ≤ (∑ i ∈ s, a i) ^ 3 / 6 * Real.exp (∑ i ∈ s, a i) :=
  (tail_bounds a s ha).2.2.2

end Tusnady.RemainderActivity
