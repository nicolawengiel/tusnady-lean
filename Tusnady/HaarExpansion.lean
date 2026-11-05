import Tusnady.HaarFunctions

/-! # Exact finite ancestor-Haar expansion of dyadic interval indicators. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators

/-- The ancestor Haar function at one of the proper ancestor depths. -/
def ancestorHaar (a : ℕ) (i : Fin (2^a)) (b : Fin a) (x : ℝ) : ℝ :=
  hI b.val (Tusnady.Dyadic.ancestorIndex i b.val b.isLt.le) x

lemma ancestorHaar_castSucc (a : ℕ) (i : Fin (2^(a+1))) (b : Fin a) (x : ℝ) :
    ancestorHaar (a+1) i b.castSucc x =
      ancestorHaar a (Tusnady.Dyadic.ancestorIndex i a (by omega)) b x := by
  unfold ancestorHaar
  simp only [Fin.coe_castSucc]
  rw [Tusnady.Dyadic.ancestorIndex_trans]

lemma ancestorHaar_last (a : ℕ) (i : Fin (2^(a+1))) (x : ℝ) :
    ancestorHaar (a+1) i (Fin.last a) x =
      hI a (Tusnady.Dyadic.ancestorIndex i a (by omega)) x := rfl

/-- A child indicator equals half the parent indicator plus a signed half
of the parent's Haar function. The sign is determined by the child itself. -/
theorem indicator_child_step (a : ℕ) (i : Fin (2^(a+1))) :
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧ ∀ x : ℝ,
      indicatorI (a+1) i x = (1/2:ℝ) *
        (indicatorI a (Tusnady.Dyadic.ancestorIndex i a (by omega)) x +
          sign * hI a (Tusnady.Dyadic.ancestorIndex i a (by omega)) x) := by
  let parent := Tusnady.Dyadic.ancestorIndex i a (by omega : a ≤ a+1)
  have hparent : parent.val = i.val/2 := by
    simp only [parent, Tusnady.Dyadic.ancestorIndex, Nat.add_sub_cancel_left, Nat.reducePow]
  have hmod := Nat.mod_add_div i.val 2
  by_cases hr : i.val%2 = 0
  · have hi : refineIndex a 1 parent 0 = i := by
      apply Fin.ext
      simp only [refineIndex, Nat.reducePow, Fin.val_zero, Nat.add_zero]
      rw [hparent]
      omega
    refine ⟨1, Or.inl rfl, ?_⟩
    intro x
    change indicatorI (a+1) i x = (1/2:ℝ)*(indicatorI a parent x+1*hI a parent x)
    conv_lhs => rw [← hi]
    have hs := indicatorI_sum_children a 1 parent x
    change indicatorI a parent x = ∑ t : Fin 2, indicatorI (a+1) (refineIndex a 1 parent t) x at hs
    rw [Fin.sum_univ_two] at hs
    unfold hI
    linarith
  · have hr1 : i.val%2 = 1 := by have h := Nat.mod_lt i.val (by omega : 0 < 2); omega
    have hi : refineIndex a 1 parent 1 = i := by
      apply Fin.ext
      simp only [refineIndex, Nat.reducePow, Fin.val_one]
      rw [hparent]
      omega
    refine ⟨-1, Or.inr rfl, ?_⟩
    intro x
    change indicatorI (a+1) i x = (1/2:ℝ)*(indicatorI a parent x+(-1)*hI a parent x)
    conv_lhs => rw [← hi]
    have hs := indicatorI_sum_children a 1 parent x
    change indicatorI a parent x = ∑ t : Fin 2, indicatorI (a+1) (refineIndex a 1 parent t) x at hs
    rw [Fin.sum_univ_two] at hs
    unfold hI
    linarith

lemma dyadicLength_succ (a : ℕ) : dyadicLength (a+1) = dyadicLength a/2 := by
  unfold dyadicLength
  rw [pow_succ]
  ring

lemma dyadicLength_succ_mul_pow (a : ℕ) : dyadicLength (a+1)*(2:ℝ)^a = (1/2:ℝ) := by
  unfold dyadicLength
  rw [pow_succ]
  field_simp

/-- Exact global ancestor expansion. The root constant is represented by
the unit-interval indicator; restricting to `[0,1)` makes it the constant 1. -/
theorem indicatorI_haar_expansion (a : ℕ) (i : Fin (2^a)) :
    ∃ signs : Fin a → ℝ, (∀ b, signs b = 1 ∨ signs b = -1) ∧ ∀ x : ℝ,
      indicatorI a i x = dyadicLength a * indicatorI 0 0 x +
        ∑ b : Fin a, signs b * (dyadicLength a*(2:ℝ)^b.val) * ancestorHaar a i b x := by
  induction a with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro b
      exact Fin.elim0 b
    · intro x
      norm_num [dyadicLength]
  | succ a ih =>
    let parent := Tusnady.Dyadic.ancestorIndex i a (by omega : a ≤ a+1)
    obtain ⟨old, hold, hformula⟩ := ih parent
    obtain ⟨sign, hsign, hstep⟩ := indicator_child_step a i
    let signs : Fin (a+1) → ℝ := Fin.lastCases sign old
    refine ⟨signs, ?_, ?_⟩
    · intro b
      refine Fin.lastCases ?_ ?_ b
      · simpa only [signs, Fin.lastCases_last] using hsign
      · intro j
        simpa only [signs, Fin.lastCases_castSucc] using hold j
    · intro x
      have hsum :
          (∑ b : Fin a, old b * (dyadicLength (a+1)*(2:ℝ)^b.val) * ancestorHaar a parent b x) =
            (1/2:ℝ) * ∑ b : Fin a, old b*(dyadicLength a*(2:ℝ)^b.val)*ancestorHaar a parent b x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        rw [dyadicLength_succ]
        ring
      rw [Fin.sum_univ_castSucc]
      simp only [signs, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.coe_castSucc, Fin.val_last,
        ancestorHaar_castSucc, ancestorHaar_last]
      change indicatorI (a+1) i x = dyadicLength (a+1)*indicatorI 0 0 x +
        ((∑ b : Fin a, old b*(dyadicLength (a+1)*(2:ℝ)^b.val)*ancestorHaar a parent b x) +
          sign*(dyadicLength (a+1)*(2:ℝ)^a)*hI a parent x)
      rw [hsum, dyadicLength_succ_mul_pow, dyadicLength_succ, hstep, hformula]
      ring

/-- Manuscript (4.8), including explicit signs and all coefficients, on the
original unit domain. The coefficient `dyadicLength a·2^b` is `2^(b-a)`. -/
theorem indicatorI_haar_expansion_unit (a : ℕ) (i : Fin (2^a)) :
    ∃ signs : Fin a → ℝ, (∀ b, signs b = 1 ∨ signs b = -1) ∧
      ∀ x ∈ Ico (0:ℝ) 1, indicatorI a i x = dyadicLength a +
        ∑ b : Fin a, signs b*(dyadicLength a*(2:ℝ)^b.val)*ancestorHaar a i b x := by
  obtain ⟨signs, hs, hformula⟩ := indicatorI_haar_expansion a i
  refine ⟨signs, hs, ?_⟩
  intro x hx
  have hroot : indicatorI 0 0 x = 1 := by
    unfold indicatorI dyadicInterval dyadicLeft dyadicLength
    norm_num
    exact hx
  have h := hformula x
  rw [hroot, mul_one] at h
  exact h

end Tusnady.Haar
