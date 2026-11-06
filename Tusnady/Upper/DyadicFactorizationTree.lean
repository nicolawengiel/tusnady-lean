import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Explicit binary-tree factorization of finite prefix incidence

A feature is a node of the complete binary tree. Point columns are root
paths; prefix rows select a disjoint canonical cover. The scalar product
is exactly prefix incidence, and both squared norms are bounded by depth.
This is the constructive core of Nikolov (2017), Lemma 7.
-/
-- Preserve the original recursive Fintype-instance unification in Lean 4.34.
-- This changes elaboration only; the kernel still checks every proof term.
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace Tusnady.Upper.DyadicFactorization

def Feature : ℕ → Type
  | 0 => Unit
  | L+1 => Unit ⊕ (Feature L ⊕ Feature L)

instance featureFintype : (L : ℕ) → Fintype (Feature L)
  | 0 => inferInstanceAs (Fintype Unit)
  | L+1 => by
      letI := featureFintype L
      exact inferInstanceAs (Fintype (Unit ⊕ (Feature L ⊕ Feature L)))

def root : (L : ℕ) → Feature L → ℝ
  | 0, _ => 1
  | _+1, Sum.inl _ => 1
  | _+1, Sum.inr _ => 0

def column : (L : ℕ) → ℕ → Feature L → ℝ
  | 0, _, _ => 1
  | _+1, _, Sum.inl _ => 1
  | L+1, i, Sum.inr (Sum.inl f) => if i < 2^L then column L i f else 0
  | L+1, i, Sum.inr (Sum.inr f) => if i < 2^L then 0 else column L (i-2^L) f

def row : (L : ℕ) → ℕ → Feature L → ℝ
  | 0, k, _ => if k = 1 then 1 else 0
  | L+1, k, Sum.inl _ => if k = 2^(L+1) then 1 else 0
  | L+1, k, Sum.inr (Sum.inl f) =>
      if k = 2^(L+1) then 0 else
        if k ≤ 2^L then row L k f else root L f
  | L+1, k, Sum.inr (Sum.inr f) =>
      if k = 2^(L+1) then 0 else
        if k ≤ 2^L then 0 else row L (k-2^L) f

lemma row_full (L : ℕ) : row L (2^L) = root L := by
  cases L with
  | zero => funext f; simp [row, root]
  | succ L => funext f; cases f with
    | inl _ => simp [row, root]
    | inr f => cases f <;> simp [row, root]

lemma root_sq_sum (L : ℕ) : (∑ f : Feature L, (root L f)^2) = 1 := by
  cases L with
  | zero => simp [Feature, root]
  | succ L => simp [Feature, root, Fintype.sum_sum_type]

lemma root_dot_column (L i : ℕ) :
    (∑ f : Feature L, root L f * column L i f) = 1 := by
  cases L with
  | zero => simp [Feature, root, column]
  | succ L => simp [Feature, root, column, Fintype.sum_sum_type]

lemma column_sq_sum (L i : ℕ) (hi : i < 2^L) :
    (∑ f : Feature L, (column L i f)^2) = (L+1 : ℕ) := by
  induction L generalizing i with
  | zero => simp [Feature, column]
  | succ L ih =>
      have hp : 2^(L+1) = 2^L+2^L := by omega
      by_cases hleft : i < 2^L
      · simp [Feature, column, Fintype.sum_sum_type, hleft, ih i hleft]
        ring
      · have hir : i-2^L < 2^L := by omega
        simp [Feature, column, Fintype.sum_sum_type, hleft, ih _ hir]
        ring

lemma row_sq_sum_le (L k : ℕ) (hk : k ≤ 2^L) :
    (∑ f : Feature L, (row L k f)^2) ≤ (L+1 : ℕ) := by
  induction L generalizing k with
  | zero =>
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hk' with rfl | rfl <;> simp [Feature, row]
  | succ L ih =>
      have hp : 2^(L+1) = 2^L+2^L := by omega
      by_cases hfull : k = 2^(L+1)
      · rw [hfull, row_full, root_sq_sum]
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
      · by_cases hleft : k ≤ 2^L
        · have h := ih k hleft
          simp only [Feature, Fintype.sum_sum_type, row, if_neg hfull, if_pos hleft,
            zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
            zero_add, add_zero]
          exact h.trans (by exact_mod_cast Nat.le_succ (L+1))
        · have hkr : k-2^L ≤ 2^L := by omega
          have h := ih (k-2^L) hkr
          simp only [Feature, Fintype.sum_sum_type, row, if_neg hfull, if_neg hleft,
            zero_pow (by decide : 2 ≠ 0), Fintype.sum_unique, zero_add, root_sq_sum]
          push_cast
          push_cast at h
          linarith

lemma row_dot_column (L k i : ℕ) (hk : k ≤ 2^L) (hi : i < 2^L) :
    (∑ f : Feature L, row L k f * column L i f) = if i < k then 1 else 0 := by
  induction L generalizing k i with
  | zero =>
      have hi0 : i = 0 := by simpa using hi
      have hk' : k = 0 ∨ k = 1 := by omega
      subst i
      rcases hk' with rfl | rfl <;> simp [Feature, row, column]
  | succ L ih =>
      have hp : 2^(L+1) = 2^L+2^L := by omega
      by_cases hfull : k = 2^(L+1)
      · subst k
        rw [row_full, root_dot_column, if_pos hi]
      · by_cases hleft : k ≤ 2^L
        · by_cases hileft : i < 2^L
          · simp [Feature, Fintype.sum_sum_type, row, column, hfull, hleft,
              hileft, ih k i hleft hileft]
          · have hik : ¬i < k := by omega
            simp [Feature, Fintype.sum_sum_type, row, column, hfull, hleft, hileft, hik]
        · by_cases hileft : i < 2^L
          · have hik : i < k := by omega
            simp [Feature, Fintype.sum_sum_type, row, column, hfull, hleft,
              hileft, root_dot_column, hik]
          · have hkr : k-2^L ≤ 2^L := by omega
            have hir : i-2^L < 2^L := by omega
            have heq : (i-2^L < k-2^L) ↔ i < k := by omega
            simp [Feature, Fintype.sum_sum_type, row, column, hfull, hleft,
              hileft, ih _ _ hkr hir, heq]

end Tusnady.Upper.DyadicFactorization
