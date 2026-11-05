import Tusnady.StepBlock
import Tusnady.TestFunction

/-! Concrete cancellation across the separated block depths. -/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace Tusnady.Witness
open Tusnady.DyadicFunctions

lemma block_depth_separation {a b : BlockIndex h} (hab : a < b) :
    a.val.val + 3 ≤ b.val.val := by
  have hab' : a.val.val < b.val.val := hab
  obtain ⟨ka, hka⟩ := a.property
  obtain ⟨kb, hkb⟩ := b.property
  omega

/-- Every nonempty block product has actual integral zero. -/
theorem integral_prod_stepBlock_eq_zero (S : Finset (BlockIndex h)) (hS : S.Nonempty)
    (z : (a : BlockIndex h) → Fin (2^a.val.val) → ℝ) :
    (∫ t, (∏ a ∈ S, stepBlock a.val.val (z a) t) ∂Tusnady.Haar.unitMeasure) = 0 := by
  classical
  let a := S.max' hS
  have ha : a ∈ S := Finset.max'_mem S hS
  have hsplit : (fun t => ∏ b ∈ S, stepBlock b.val.val (z b) t) =
      (fun t => (∏ b ∈ S.erase a, stepBlock b.val.val (z b) t) *
        stepBlock a.val.val (z a) t) := by
    funext t
    exact (Finset.prod_erase_mul _ _ ha).symm
  rw [hsplit]
  apply integral_mul_stepBlock_eq_zero
  intro i
  refine ⟨∏ b ∈ S.erase a, stepBlock b.val.val (z b) (dyadicLeft a.val.val i), ?_⟩
  apply finiteProduct_eqOn_constant _ _ _ _ (by
    constructor
    · exact le_rfl
    · exact lt_add_of_pos_right _ (dyadicLength_pos _))
  intro b hb
  have hba : b < a := lt_of_le_of_ne (Finset.le_max' S b (Finset.mem_of_mem_erase hb))
    (Finset.ne_of_mem_erase hb)
  exact stepBlock_constant_on_finer _ _ (block_depth_separation hba) (z b) i

/-- Exact normalization of the separated positive products. -/
theorem integral_positive_stepProduct (c : ℝ)
    (z : (a : BlockIndex h) → Fin (2^a.val.val) → ℝ)
    (hz : ∀ a i, |z a i| ≤ 1) :
    (∫ t, (∏ a : BlockIndex h, (1+c*stepBlock a.val.val (z a) t))
      ∂Tusnady.Haar.unitMeasure) = 1 := by
  classical
  have heq : (fun t => ∏ a : BlockIndex h, (1+c*stepBlock a.val.val (z a) t)) =
      (fun t => ∑ S : Finset (BlockIndex h), c^S.card *
        ∏ a ∈ S, stepBlock a.val.val (z a) t) := by
    funext t
    exact product_expansion _ _
  rw [heq, integral_finset_sum]
  · simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single ∅]
    · simp
    · intro S _ hS
      rw [integral_prod_stepBlock_eq_zero S (Finset.nonempty_iff_ne_empty.mpr hS), mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ ∅))
  · intro S _
    exact (prod_stepBlock_integrable S (fun a => a.val.val) z hz).const_mul _

end Tusnady.Witness
