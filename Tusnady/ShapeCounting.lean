import Tusnady.RemainderCounting
import Tusnady.TestFunction
import Tusnady.SamplingSpaceCounting

/-! Genuine shell and block cardinalities, with explicit dimension-only
constants. The lower count is an explicit grid of 3-divisible depths. -/

noncomputable section
open scoped BigOperators
namespace Tusnady.Dyadic

theorem card_shape_le (k h : ℕ) : Fintype.card (Shape (k + 1) h) ≤ (h + 1) ^ k := by
  apply RemainderCounting.card_fixed_sum_le k h Shape.depth
  · intro r s h
    exact Shape.ext h
  · exact Shape.sum_depth

def gridShape (k q : ℕ) (t : Fin k → Fin (q / (k + 1) + 1)) : Shape (k + 1) (3 * q) where
  depth := Fin.cons (3 * (q - ∑ i, (t i).val)) (fun i => 3 * (t i).val)
  sum_depth := by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← Finset.mul_sum]
    rw [← Nat.mul_add, Nat.sub_add_cancel (SamplingSpace.lowerTail_sum_le k q t)]
  three_dvd_depth := by
    intro i
    exact Fin.cases (dvd_mul_right 3 _) (fun j => dvd_mul_right 3 _) i

theorem gridShape_injective (k q : ℕ) : Function.Injective (gridShape k q) := by
  intro t u h
  funext i
  apply Fin.ext
  have hi := congrArg (fun r : Shape (k + 1) (3 * q) => r.depth i.succ) h
  simp only [gridShape, Fin.cons_succ] at hi
  omega

theorem card_shape_grid_lower (k q : ℕ) :
    (q / (k + 1) + 1) ^ k ≤ Fintype.card (Shape (k + 1) (3 * q)) := by
  simpa only [Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective _ (gridShape_injective k q)

/-- The lower constant depends only on the dimension k+1. -/
theorem card_shape_lower (k h : ℕ) (hh : 3 ∣ h) :
    (1 / ((3 : ℝ) * (k + 1 : ℕ)) ^ k) * (h + 1 : ℕ) ^ k ≤
      (Fintype.card (Shape (k + 1) h) : ℝ) := by
  obtain ⟨q, rfl⟩ := hh
  have hgrid := card_shape_grid_lower k q
  have hsmall : 3 * q + 1 ≤ (3 * (k + 1)) * (q / (k + 1) + 1) := by
    have hd : q < (k + 1) * (q / (k + 1) + 1) := by
      have hr := Nat.mod_lt q (Nat.succ_pos k)
      have he := Nat.mod_add_div q (k + 1)
      nlinarith
    nlinarith
  have hp : ((3 * q + 1 : ℕ) : ℝ) ^ k ≤
      (((3 : ℝ) * (k + 1 : ℕ)) * (q / (k + 1) + 1 : ℕ)) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hsmall
  rw [mul_pow] at hp
  have hbase : (0 : ℝ) < ((3 : ℝ) * (k + 1 : ℕ)) ^ k := by positivity
  have hgridR : ((q / (k + 1) + 1 : ℕ) : ℝ) ^ k ≤
      (Fintype.card (Shape (k + 1) (3 * q)) : ℝ) := by exact_mod_cast hgrid
  simp only [one_div]
  calc
    _ ≤ (((3 : ℝ) * (k + 1 : ℕ)) ^ k)⁻¹ *
        ((((3 : ℝ) * (k + 1 : ℕ)) ^ k) * (q / (k + 1) + 1 : ℕ) ^ k) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = ((q / (k + 1) + 1 : ℕ) : ℝ) ^ k := by field_simp
    _ ≤ _ := hgridR

end Tusnady.Dyadic

namespace Tusnady.Witness
open Dyadic

theorem card_shapesInBlock_le (k h : ℕ) (j : Fin (k + 2)) (a : BlockIndex h) :
    Fintype.card (ShapesInBlock j a) ≤ (h + 1) ^ k := by
  let f : ShapesInBlock j a → Fin (k + 1) → ℕ := fun r i => r.val.depth (j.succAbove i)
  have hf : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply Shape.ext
    funext i
    refine Fin.succAboveCases j ?_ (fun l => ?_) i
    · rw [r.property, s.property]
    · exact congrFun hrs l
  have hsum : ∀ r : ShapesInBlock j a, ∑ i, f r i = h - a.val.val := by
    intro r
    have hh := r.val.sum_depth
    rw [Fin.sum_univ_succAbove _ j, r.property] at hh
    change a.val.val + ∑ i, f r i = h at hh
    omega
  exact (RemainderCounting.card_fixed_sum_le k (h - a.val.val) f hf hsum).trans
    (Nat.pow_le_pow_left (Nat.succ_le_succ (Nat.sub_le h _)) k)

end Tusnady.Witness
