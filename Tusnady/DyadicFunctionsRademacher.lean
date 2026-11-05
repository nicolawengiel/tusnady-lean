import Tusnady.DyadicFunctionsScaling

/-! # The concrete Walsh patches equal the standard Rademacher product. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.DyadicFunctions
open MeasureTheory Set
open scoped BigOperators

/-- Standard Rademacher function on the nonnegative real axis, extended
by the natural floor convention outside it. Only nonnegative arguments are
used in the localized product identification. -/
def rademacher (j : ℕ) (x : ℝ) : ℝ := (-1:ℝ) ^ ⌊(2:ℝ)^j*x⌋₊

lemma floor_two_on_cell (i : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    ⌊2*p⌋₊ = i.val / 4 := by
  have hnonneg : 0 ≤ 2*p := by linarith [(baseCell_subset_unit i hp).1]
  apply (Nat.floor_eq_iff hnonneg).2
  change cellLo i ≤ p ∧ p < cellHi i at hp
  fin_cases i <;> norm_num [cellLo, cellHi] at hp ⊢ <;>
    constructor <;> linarith [hp.1, hp.2]

lemma floor_four_on_cell (i : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    ⌊4*p⌋₊ = i.val / 2 := by
  have hnonneg : 0 ≤ 4*p := by linarith [(baseCell_subset_unit i hp).1]
  apply (Nat.floor_eq_iff hnonneg).2
  change cellLo i ≤ p ∧ p < cellHi i at hp
  fin_cases i <;> norm_num [cellLo, cellHi] at hp ⊢ <;>
    constructor <;> linarith [hp.1, hp.2]

lemma floor_eight_on_cell (i : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    ⌊8*p⌋₊ = i.val := by
  have hnonneg : 0 ≤ 8*p := by linarith [(baseCell_subset_unit i hp).1]
  apply (Nat.floor_eq_iff hnonneg).2
  change cellLo i ≤ p ∧ p < cellHi i at hp
  fin_cases i <;> norm_num [cellLo, cellHi] at hp ⊢ <;>
    constructor <;> linarith [hp.1, hp.2]

/-- The eight signs are exactly the product of the first three Rademachers. -/
lemma rademacher_product_on_cell (i : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    rademacher 1 p * rademacher 2 p * rademacher 3 p = walshSign i := by
  unfold rademacher
  norm_num only [pow_one, Nat.reduceAdd, Nat.cast_ofNat, Nat.reducePow]
  rw [floor_two_on_cell i p hp, floor_four_on_cell i p hp, floor_eight_on_cell i p hp]
  fin_cases i <;> norm_num [walshSign]

/-- The genuine product definition, with its full pointwise boundary behavior. -/
theorem qBase_eq_rademacher (p : ℝ) :
    qBase p = (Ico (0:ℝ) 1).indicator
      (fun x => rademacher 1 x * rademacher 2 x * rademacher 3 x) p := by
  by_cases hp : p ∈ Ico (0:ℝ) 1
  · obtain ⟨i, hi⟩ := exists_baseCell p hp
    rw [qBase_on_cell i p hi, Set.indicator_of_mem hp,
      rademacher_product_on_cell i p hi]
  · rw [qBase_zero_outside p hp, Set.indicator_of_notMem hp]

/-- Translating by a dyadic index and rescaling shifts the Rademacher
level; the integer part contributes an even exponent. -/
theorem rademacher_dyadic_affine (a k n : ℕ) (hk : 0 < k) (u : ℝ) (hu : 0 ≤ u) :
    rademacher (a+k) (((n:ℝ)+u)/(2:ℝ)^a) = rademacher k u := by
  have hpowpos : (0:ℝ) < 2^a := by positivity
  have harg : (2:ℝ)^(a+k) * (((n:ℝ)+u)/(2:ℝ)^a) =
      (2:ℝ)^k*u + ((2^k*n : ℕ):ℝ) := by
    rw [pow_add]
    push_cast
    field_simp
    ring
  unfold rademacher
  rw [harg, Nat.floor_add_natCast (by positivity), pow_add]
  have heven : (-1:ℝ)^(2^k*n) = 1 := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    rw [pow_succ]
    rw [show 2^t*2*n = 2*(2^t*n) by ring, pow_mul]
    norm_num
  rw [heven, mul_one]

lemma dyadic_normalized_inverse (a : ℕ) (i : Fin (2^a)) (x : ℝ) :
    x = ((i.val : ℝ) + (x-dyadicLeft a i)/dyadicLength a)/(2:ℝ)^a := by
  unfold dyadicLeft dyadicLength
  field_simp
  ring

/-- The scaled concrete function equals the precise manuscript definition
`1_I · ρ_(a+1) · ρ_(a+2) · ρ_(a+3)` at every real point. -/
theorem qI_eq_rademacher (a : ℕ) (i : Fin (2^a)) (x : ℝ) :
    qI a i x = (dyadicInterval a i).indicator
      (fun x => rademacher (a+1) x * rademacher (a+2) x * rademacher (a+3) x) x := by
  by_cases hx : x ∈ dyadicInterval a i
  · have hu : (x-dyadicLeft a i)/dyadicLength a ∈ Ico (0:ℝ) 1 :=
      (normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).2 hx
    have hlevel : ∀ k : ℕ, 0 < k → rademacher (a+k) x =
        rademacher k ((x-dyadicLeft a i)/dyadicLength a) := by
      intro k hk
      conv_lhs => rw [dyadic_normalized_inverse a i x]
      exact rademacher_dyadic_affine a k i.val hk _ hu.1
    unfold qI q
    rw [qBase_eq_rademacher, Set.indicator_of_mem hu, Set.indicator_of_mem hx,
      hlevel 1 (by omega), hlevel 2 (by omega), hlevel 3 (by omega)]
  · have hu : (x-dyadicLeft a i)/dyadicLength a ∉ Ico (0:ℝ) 1 :=
      fun h => hx ((normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).1 h)
    unfold qI q
    rw [qBase_zero_outside _ hu, Set.indicator_of_notMem hx]

end Tusnady.DyadicFunctions

