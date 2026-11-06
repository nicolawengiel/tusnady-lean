import Tusnady.WalshDerivative
import Mathlib.Data.Finset.Powerset

/-! The covering and derivative-energy arguments in Lemma 2.3(iii). -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh
attribute [local instance] Classical.propDecidable

/-- If each target is covered, summing its nonnegative weight once is
bounded by the sum over all covers. No independence/counting assumption
is used: the inequality is proved by rearranging the finite sums. -/
theorem cover_sum_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s u : Finset α) (t : Finset β) (a : α → ℝ) (R : β → α → Prop)
    (hsu : s ⊆ u) (ha : ∀ i ∈ u, 0 ≤ a i)
    (hcover : ∀ i ∈ s, ∃ j ∈ t, R j i) :
    (∑ i ∈ s, a i) ≤ ∑ j ∈ t, ∑ i ∈ u, if R j i then a i else 0 := by
  classical
  calc
    (∑ i ∈ s, a i) ≤ ∑ i ∈ s, ∑ j ∈ t, if R j i then a i else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨j, hj, hji⟩ := hcover i hi
      have h := Finset.single_le_sum (s := t) (f := fun j => if R j i then a i else 0)
        (fun k _ => by
          by_cases hR : R k i
          · simpa only [if_pos hR] using ha i (hsu hi)
          · simp only [if_neg hR, le_refl]) hj
      simpa only [if_pos hji] using h
    _ = ∑ j ∈ t, ∑ i ∈ s, if R j i then a i else 0 := Finset.sum_comm
    _ ≤ ∑ j ∈ t, ∑ i ∈ u, if R j i then a i else 0 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum_of_subset_of_nonneg hsu
      intro i hi _
      by_cases hR : R j i
      · simpa only [if_pos hR] using ha i hi
      · simp only [if_neg hR, le_refl]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every nonempty subset of E is counted by at least one first derivative. -/
theorem first_activity_le_derivative_energy (F : Cube ι → ℝ) (E : Finset ι) :
    (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S ⊆ E ∧ S.Nonempty),
      coefficient F S ^ 2) ≤ ∑ i ∈ E, mean (fun x => derivative F i x ^ 2) := by
  classical
  have h := cover_sum_le
    (Finset.univ.filter (fun S : Finset ι => S ⊆ E ∧ S.Nonempty))
    Finset.univ E (fun S => coefficient F S ^ 2) (fun i S => i ∈ S)
    (Finset.subset_univ _) (fun S _ => sq_nonneg _) (by
      intro S hS
      obtain ⟨hSE, hne⟩ := (Finset.mem_filter.mp hS).2
      obtain ⟨i, hi⟩ := hne
      exact ⟨i, hSE hi, hi⟩)
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_parseval, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hs : i ∈ S <;> simp [hs]

/-- A uniform first-difference bound gives the first Walsh activity bound. -/
theorem first_activity_of_derivative_bound (F : Cube ι → ℝ) (E : Finset ι)
    {theta : ℝ} (htheta : 0 ≤ theta)
    (hder : ∀ i ∈ E, ∀ x, |derivative F i x| ≤ theta) :
    (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S ⊆ E ∧ S.Nonempty),
      coefficient F S ^ 2) ≤ theta ^ 2 * (E.card : ℝ) := by
  calc
    _ ≤ ∑ i ∈ E, mean (fun x => derivative F i x ^ 2) :=
      first_activity_le_derivative_energy F E
    _ ≤ ∑ _i ∈ E, theta ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mean_const (ι := ι) (theta ^ 2)]
      apply mean_mono
      intro x
      have h := hder i hi x
      have hs := sq_abs (derivative F i x)
      nlinarith [abs_nonneg (derivative F i x)]
    _ = _ := by simp [mul_comm]

/-- Every degree-at-least-three subset is covered by a triple of E.
The analytic triple-derivative identity is a separate proved obligation. -/
theorem third_activity_le_triple_energy (F : Cube ι → ℝ) (E : Finset ι) :
    (∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => S ⊆ E ∧ 3 ≤ S.card),
      coefficient F S ^ 2) ≤
      ∑ K ∈ E.powersetCard 3,
        ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => K ⊆ S), coefficient F S ^ 2 := by
  classical
  have h := cover_sum_le
    (Finset.univ.filter (fun S : Finset ι => S ⊆ E ∧ 3 ≤ S.card))
    Finset.univ (E.powersetCard 3) (fun S => coefficient F S ^ 2) (fun K S => K ⊆ S)
    (Finset.subset_univ _) (fun S _ => sq_nonneg _) (by
      intro S hS
      obtain ⟨hSE, h3⟩ := (Finset.mem_filter.mp hS).2
      obtain ⟨K, hKS, hKcard⟩ := Finset.exists_subset_card_eq h3
      exact ⟨K, Finset.mem_powersetCard.mpr ⟨hKS.trans hSE, hKcard⟩, hKS⟩)
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro K _
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hs : K ⊆ S <;> simp [hs]

end Tusnady.Walsh
