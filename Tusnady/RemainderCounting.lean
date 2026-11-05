import Tusnady.Shell
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

/-! # Actual deficit and join counts in Main.pdf Lemma 4.4

The proof encodes all but one coordinate of a nonnegative vector with
fixed sum. It avoids stars-and-bars, and proves slightly sharper bounds
`(e+1)^(d-1)` and `(e+1)^(d-2)` for the actual shape subtypes.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.RemainderCounting
attribute [local instance] Classical.propDecidable

instance shapesBelowFintype {d h : ℕ} (j : Fin d → ℕ) :
    Fintype (Dyadic.ShapesBelow (h := h) j) := by
  unfold Dyadic.ShapesBelow
  infer_instance

def sumSliceCode {A : Type*} (k n : ℕ) (f : A → Fin (k + 1) → ℕ)
    (hsum : ∀ a, ∑ i, f a i = n) (a : A) : Fin k → Fin (n + 1) :=
  fun i => ⟨f a i.succ, Nat.lt_succ_of_le (by
    have h := Finset.single_le_sum (fun j _ => Nat.zero_le (f a j)) (Finset.mem_univ i.succ)
    rwa [hsum a] at h)⟩

theorem sumSliceCode_injective {A : Type*} (k n : ℕ) (f : A → Fin (k + 1) → ℕ)
    (hf : Function.Injective f) (hsum : ∀ a, ∑ i, f a i = n) :
    Function.Injective (sumSliceCode k n f hsum) := by
  intro a b hab
  apply hf
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have ha := hsum a
    have hb := hsum b
    simp only [Fin.sum_univ_succ] at ha hb
    have ht : (∑ j : Fin k, f a j.succ) = ∑ j : Fin k, f b j.succ := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg Fin.val (congrFun hab j)
    omega
  · exact congrArg Fin.val (congrFun hab j)

theorem card_fixed_sum_le {A : Type*} [Fintype A] (k n : ℕ)
    (f : A → Fin (k + 1) → ℕ) (hf : Function.Injective f)
    (hsum : ∀ a, ∑ i, f a i = n) : Fintype.card A ≤ (n + 1) ^ k := by
  have h := Fintype.card_le_of_injective _ (sumSliceCode_injective k n f hf hsum)
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

theorem card_fixed_sum_fixed_zero_le {A : Type*} [Fintype A] (k n : ℕ)
    (f : A → Fin (k + 2) → ℕ) (hf : Function.Injective f)
    (hsum : ∀ a, ∑ i, f a i = n) (p : Fin (k + 2)) (hp : ∀ a, f a p = 0) :
    Fintype.card A ≤ (n + 1) ^ k := by
  let g : A → Fin (k + 1) → ℕ := fun a i => f a (p.succAbove i)
  apply card_fixed_sum_le k n g
  · intro a b hab
    apply hf
    funext i
    refine Fin.succAboveCases p ?_ (fun j => ?_) i
    · rw [hp a, hp b]
    · exact congrFun hab j
  · intro a
    have h := hsum a
    rw [Fin.sum_univ_succAbove _ p, hp a, zero_add] at h
    exact h

theorem card_shapesBelow_le (k h e : ℕ) (j : Fin (k + 1) → ℕ)
    (hj : ∑ i, j i = h + e) :
    Fintype.card (Dyadic.ShapesBelow (h := h) j) ≤ (e + 1) ^ k := by
  apply card_fixed_sum_le k e (Dyadic.deficit j) (Dyadic.deficit_injective j)
  intro r
  rw [Dyadic.sum_deficit, hj]
  omega

theorem card_shapesBelow_fixed_coordinate_le (k h e : ℕ) (j : Fin (k + 2) → ℕ)
    (hj : ∑ i, j i = h + e) (p : Fin (k + 2)) :
    Fintype.card {r : Dyadic.ShapesBelow (h := h) j // r.val.depth p = j p} ≤
      (e + 1) ^ k := by
  let f : {r : Dyadic.ShapesBelow (h := h) j // r.val.depth p = j p} →
      Fin (k + 2) → ℕ := fun r => Dyadic.deficit j r.val
  apply card_fixed_sum_fixed_zero_le k e f (p := p)
    ((Dyadic.deficit_injective j).comp Subtype.val_injective)
  · intro r
    rw [Dyadic.sum_deficit, hj]
    omega
  · intro r
    change j p - r.val.val.depth p = 0
    rw [r.property, Nat.sub_self]

/-- All actual depth vectors at a specified join level. The divisibility
condition only shrinks this finite type; the count does not assume it. -/
abbrev JoinVectors (d H : ℕ) :=
  {j : Fin d → Fin (H + 1) // (∑ i, (j i).val) = H ∧ ∀ i, 3 ∣ (j i).val}

theorem card_joinVectors_le (k H : ℕ) :
    Fintype.card (JoinVectors (k + 1) H) ≤ (H + 1) ^ k := by
  apply card_fixed_sum_le k H (fun j i => (j.val i).val)
  · intro j l hjl
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hjl i)
  · exact fun j => j.property.1

theorem card_joins_excess_le (k h e : ℕ) (he : e ≤ k * h) :
    Fintype.card (JoinVectors (k + 1) (h + e)) ≤
      (k + 1) ^ k * (h + 1) ^ k := by
  calc
    _ ≤ (h + e + 1) ^ k := card_joinVectors_le k (h + e)
    _ ≤ ((k + 1) * (h + 1)) ^ k := by
      apply Nat.pow_le_pow_left
      nlinarith
    _ = _ := Nat.mul_pow _ _ _

end Tusnady.RemainderCounting
