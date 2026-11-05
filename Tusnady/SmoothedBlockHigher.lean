import Tusnady.SmoothedBlock
import Tusnady.WalshHigherDerivative
import Tusnady.FiniteDifference
import Mathlib.Data.Nat.Choose.Bounds

/-! Third finite derivatives and nonlinear activity of the actual tanh block. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A scalar function applied to a specified set of remaining signs. -/
def blockOn (A : Finset ι) (f : ℝ → ℝ) (theta : ℝ) (x : Cube ι) : ℝ :=
  f (theta * ∑ j ∈ A, bitSign (x j))

theorem sum_sign_update_on (A : Finset ι) {i : ι} (hi : i ∈ A)
    (x : Cube ι) (b : Bool) :
    (∑ j ∈ A, bitSign (Function.update x i b j)) =
      bitSign b + ∑ j ∈ A.erase i, bitSign (x j) := by
  have hf : (fun j => bitSign (Function.update x i b j)) =
      Function.update (fun j => bitSign (x j)) i (bitSign b) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp only [Function.update_of_ne hj]
  rw [hf, Finset.sum_update_of_mem hi]
  simp only [Finset.sdiff_singleton_eq_erase]

/-- The actual cube difference removes one coordinate from the scalar sum
and applies the actual scalar central difference. -/
theorem derivative_blockOn (A : Finset ι) (f : ℝ → ℝ) (theta : ℝ)
    {i : ι} (hi : i ∈ A) (x : Cube ι) :
    derivative (blockOn A f theta) i x =
      blockOn (A.erase i) (centralDifference f theta) theta x := by
  unfold derivative blockOn centralDifference
  rw [sum_sign_update_on A hi, sum_sign_update_on A hi]
  have hp : theta * (bitSign true + ∑ j ∈ A.erase i, bitSign (x j)) =
      theta * (∑ j ∈ A.erase i, bitSign (x j)) + theta := by
    rw [show bitSign true = (1 : ℝ) from rfl]
    ring
  have hm : theta * (bitSign false + ∑ j ∈ A.erase i, bitSign (x j)) =
      theta * (∑ j ∈ A.erase i, bitSign (x j)) - theta := by
    rw [show bitSign false = (-1 : ℝ) from rfl]
    ring
  rw [hp, hm]

/-- The spectral formula is an actual iterated scalar finite difference,
proved by induction using the actual Boolean update operation. -/
theorem subsetDerivative_blockOn (K : Finset ι) (f : ℝ → ℝ) (theta : ℝ) (x : Cube ι) :
    subsetDerivative K (blockOn Finset.univ f theta) x =
      blockOn (Finset.univ \ K) (iterDifference theta K.card f) theta x := by
  induction K using Finset.induction_on generalizing x with
  | empty => simp only [subsetDerivative_empty, Finset.sdiff_empty, Finset.card_empty, iterDifference]
  | @insert i K hi ih =>
    rw [← subsetDerivative_insert K (blockOn Finset.univ f theta) i hi x]
    have hf : subsetDerivative K (blockOn Finset.univ f theta) =
        blockOn (Finset.univ \ K) (iterDifference theta K.card f) theta := by
      funext y
      exact ih y
    rw [hf, derivative_blockOn _ _ _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)]
    have hsets : ((Finset.univ : Finset ι) \ K).erase i = Finset.univ \ insert i K := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_insert]
      tauto
    rw [hsets, Finset.card_insert_of_notMem hi]
    rfl

/-- The required actual third-difference bound for every triple of
coordinates, including all coincidences among the other signs. -/
theorem smoothedBlock_third_derivative_bound {theta : ℝ} (htheta : 0 ≤ theta)
    (K : Finset ι) (hK : K.card = 3) (x : Cube ι) :
    |subsetDerivative K (smoothedBlock theta) x| ≤ 2 * theta ^ 3 := by
  have hF : (smoothedBlock theta : Cube ι → ℝ) = blockOn Finset.univ Real.tanh theta := rfl
  rw [hF, subsetDerivative_blockOn, hK]
  exact abs_tanh_third_difference htheta _

/-- Lemma 2.3(iii), cubic Walsh activity for the actual smoothed block.
The factor four from the derivative bound is absorbed by 3! in the exact
number of triples, retaining the manuscript's constant one. -/
theorem smoothedBlock_third_activity {theta : ℝ} (htheta : 0 ≤ theta) (E : Finset ι) :
    (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S ⊆ E ∧ 3 ≤ S.card),
      coefficient (smoothedBlock theta) S ^ 2) ≤ theta ^ 6 * (E.card : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ K ∈ E.powersetCard 3,
        ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => K ⊆ S),
          coefficient (smoothedBlock theta) S ^ 2 :=
      third_activity_le_triple_energy _ E
    _ = ∑ K ∈ E.powersetCard 3,
        mean (fun x => subsetDerivative K (smoothedBlock theta) x ^ 2) := by
      apply Finset.sum_congr rfl
      intro K _
      exact (subsetDerivative_parseval K _).symm
    _ ≤ ∑ _K ∈ E.powersetCard 3, (2 * theta ^ 3) ^ 2 := by
      apply Finset.sum_le_sum
      intro K hK
      rw [← mean_const (ι := ι) ((2 * theta ^ 3) ^ 2)]
      apply mean_mono
      intro x
      have h := smoothedBlock_third_derivative_bound htheta K (Finset.mem_powersetCard.mp hK).2 x
      have hp : 0 ≤ 2 * theta ^ 3 := by positivity
      nlinarith [sq_abs (subsetDerivative K (smoothedBlock theta) x),
        abs_nonneg (subsetDerivative K (smoothedBlock theta) x)]
    _ = (E.card.choose 3 : ℝ) * (2 * theta ^ 3) ^ 2 := by simp
    _ ≤ theta ^ 6 * (E.card : ℝ) ^ 3 := by
      have hcount := Nat.choose_le_pow_div (α := ℝ) 3 E.card
      norm_num at hcount
      have hn : (0 : ℝ) ≤ E.card := by positivity
      have ht : 0 ≤ theta ^ 6 := by positivity
      have hprod := mul_le_mul_of_nonneg_right hcount (show 0 ≤ (2 * theta ^ 3) ^ 2 by positivity)
      nlinarith [mul_nonneg ht (pow_nonneg hn 3)]

end Tusnady.Walsh
