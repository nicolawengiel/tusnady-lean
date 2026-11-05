import Tusnady.DyadicIntervals
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Join cells and their ancestor-box families

The discrete part of Manuscript Lemma 4.2(a): each join cell determines one
box of each shape by taking ancestors; distinct join cells determine distinct
families. Hence exactly `2^(h+e)` such ancestor families exist.

An analytic identification of these families with the nonzero products of
localized Walsh functions still requires the real interval and function
lemmas. The definition here does not assert that missing identification.
-/

set_option autoImplicit false

namespace Tusnady.Dyadic

variable {d h : ℕ}

/-- One dyadic box index for each shape of a finite family. -/
abbrev ShapeBoxFamily (S : Finset (Shape d h)) := ∀ r : S, CellIndices r.val.depth

/-- The box family containing a fixed join cell, given explicitly by ancestors. -/
def boxFamilyFromCell (S : Finset (Shape d h))
    (x : CellIndices (join S)) : ShapeBoxFamily S :=
  fun r k => ancestorIndex (x k) (r.val.depth k) (depth_le_join S r.property k)

/-- The join is attained in each coordinate, so its cells can be recovered
from their ancestor families. -/
theorem boxFamilyFromCell_injective (S : Finset (Shape d h)) (hS : S.Nonempty) :
    Function.Injective (boxFamilyFromCell S) := by
  intro x y hxy
  funext k
  obtain ⟨r, hr, hmax⟩ := Finset.exists_mem_eq_sup S hS (fun r => r.depth k)
  have hk := congrArg (fun F : ShapeBoxFamily S => (F ⟨r, hr⟩ k).val) hxy
  change (x k).val / 2 ^ (join S k - r.depth k) =
    (y k).val / 2 ^ (join S k - r.depth k) at hk
  have hmax' : join S k = r.depth k := hmax
  simp only [hmax', Nat.sub_self, pow_zero, Nat.div_one] at hk
  exact Fin.ext hk

/-- The exact bijection between join cells and the ancestor families they
produce, with no counting estimate as an assumption. -/
noncomputable def joinCellAncestorEquiv (S : Finset (Shape d h)) (hS : S.Nonempty) :
    CellIndices (join S) ≃ Set.range (boxFamilyFromCell S) :=
  Equiv.ofInjective (boxFamilyFromCell S) (boxFamilyFromCell_injective S hS)

/-- There are exactly `2^(h+e)` ancestor box families associated with a
nonempty shape set. This is the discrete cardinality part of Lemma 4.2(a). -/
theorem card_ancestorFamilies (S : Finset (Shape d h)) (hS : S.Nonempty) :
    Nat.card (Set.range (boxFamilyFromCell S)) = 2 ^ (h + excess S) := by
  rw [← Nat.card_congr (joinCellAncestorEquiv S hS), Nat.card_eq_fintype_card]
  exact card_joinCells S hS

end Tusnady.Dyadic
