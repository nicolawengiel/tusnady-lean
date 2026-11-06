import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Finite inclusion-exclusion for closed-box counts

Each coordinate contributes an upper closed indicator minus a lower strict
indicator.  Their product is expanded over all Boolean corner choices.  This
file is purely finite algebra; no geometric distinctness or boundary
assumption is involved.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.Boxes

variable {ι α : Type*} [Fintype ι] [Fintype α]

/-- Inclusion-exclusion coefficient for the coordinates using a lower cutoff. -/
def cornerSign (ε : ι → Bool) : ℝ :=
  ∏ j, if ε j then (-1 : ℝ) else 1

@[simp] theorem abs_cornerSign (ε : ι → Bool) : |cornerSign ε| = 1 := by
  classical
  rw [cornerSign, Finset.abs_prod]
  apply Finset.prod_eq_one
  intro j _
  cases ε j <;> norm_num

variable [DecidableEq ι]

/-- Exact Boolean-corner expansion, including zero coordinates. -/
theorem prod_sub_eq_sum_corners (f g : ι → ℝ) :
    (∏ j, (f j - g j)) =
      ∑ ε : ι → Bool, cornerSign ε * ∏ j, if ε j then g j else f j := by
  classical
  calc
    _ = ∏ j, ∑ b : Bool,
        (if b then (-1 : ℝ) else 1) * (if b then g j else f j) := by
      apply Finset.prod_congr rfl
      intro j _
      simp [sub_eq_add_neg, add_comm]
    _ = ∑ ε : ι → Bool, ∏ j,
        (if ε j then (-1 : ℝ) else 1) * (if ε j then g j else f j) :=
      Fintype.prod_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ε _
      rw [Finset.prod_mul_distrib]
      rfl

/-- The same expansion after summing arbitrary real weights over the points. -/
theorem weighted_prod_sub_eq_sum_corners
    (χ : α → ℝ) (f g : α → ι → ℝ) :
    (∑ i, χ i * ∏ j, (f i j - g i j)) =
      ∑ ε : ι → Bool, cornerSign ε * ∑ i, χ i * ∏ j, if ε j then g i j else f i j := by
  classical
  calc
    _ = ∑ i, ∑ ε : ι → Bool,
        cornerSign ε * (χ i * ∏ j, if ε j then g i j else f i j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [prod_sub_eq_sum_corners, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ε _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro ε _
      rw [Finset.mul_sum]

/-- There are exactly 2^d corner choices in d coordinates. -/
theorem card_cornerChoices (d : ℕ) : Fintype.card (Fin d → Bool) = 2^d := by
  simp

omit [DecidableEq ι] in
/-- Product indicators retain every closed boundary, including empty products. -/
theorem prod_ite_one_zero_eq (p : ι → Prop) [DecidablePred p] :
    (∏ j, if p j then (1 : ℝ) else 0) = if ∀ j, p j then 1 else 0 := by
  classical
  by_cases hp : ∀ j, p j
  · simp [hp]
  · obtain ⟨j, hj⟩ := not_forall.mp hp
    have hz : (∏ j, if p j then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])
    simp [hp, hz]

/-- The lower cutoff is strict because the box itself is closed. -/
theorem closed_interval_indicator_sub (a b x : ℝ) (hab : a ≤ b) :
    (if x ≤ b then (1 : ℝ) else 0) - (if x < a then 1 else 0) =
      if a ≤ x ∧ x ≤ b then 1 else 0 := by
  by_cases hxa : x < a
  · have hxb : x ≤ b := hxa.le.trans hab
    simp [hxa, hxb, not_le.mpr hxa]
  · simp [hxa, le_of_not_gt hxa]

/-- A simultaneous bound on all corner counts controls the box count with
the universal factor 2^d.  No assumption on the point weights is needed. -/
theorem abs_weighted_prod_sub_le
    (χ : α → ℝ) (f g : α → ι → ℝ) (B : ℝ)
    (hcorners : ∀ ε : ι → Bool,
      |∑ i, χ i * ∏ j, if ε j then g i j else f i j| ≤ B) :
    |∑ i, χ i * ∏ j, (f i j - g i j)| ≤ (2 : ℝ)^(Fintype.card ι) * B := by
  classical
  rw [weighted_prod_sub_eq_sum_corners]
  calc
    _ ≤ ∑ ε : ι → Bool,
        |cornerSign ε * ∑ i, χ i * ∏ j, if ε j then g i j else f i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ε : ι → Bool, |∑ i, χ i * ∏ j, if ε j then g i j else f i j| := by
      simp only [abs_mul, abs_cornerSign, one_mul]
    _ ≤ ∑ _ε : ι → Bool, B := Finset.sum_le_sum fun ε _ => hcorners ε
    _ = _ := by simp

end Tusnady.Boxes
