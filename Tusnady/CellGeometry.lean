import Tusnady.CellLocation
import Tusnady.Shell
import Tusnady.DyadicCells

/-!
# Actual shell-family intersection cells

Compatibility means a genuine common real point of the actual shell boxes.
It is proved equivalent to the nonzero Walsh-product condition and to being
an ancestor family of a unique join cell. Thus the cell bijection is not
encoded as a compatibility assumption.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.Dyadic Tusnady.DyadicFunctions Tusnady.Haar Tusnady.Witness
open scoped BigOperators

variable {d h : ℕ}

abbrev Family (S : Finset (Shape d h)) := ShapeBoxFamily S

def familyShell (S : Finset (Shape d h)) (c : Family S) (r : S) : Shell d h := ⟨r.val,c r⟩

def familyProduct (S : Finset (Shape d h)) (c : Family S) (x : Tusnady.Point d) : ℝ :=
  ∏ r : S, qShell (familyShell S c r) x

/-- A genuine nonempty intersection of actual real shell boxes. -/
def Compatible (S : Finset (Shape d h)) (c : Family S) : Prop :=
  ∃ x : Tusnady.Point d, ∀ r : S, x ∈ shellBox (familyShell S c r)

lemma qShell_ne_zero_iff (R : Shell d h) (x : Tusnady.Point d) : qShell R x ≠ 0 ↔ x ∈ shellBox R := by
  constructor
  · intro h
    by_contra hx
    exact h (qShell_zero_outside R x hx)
  · intro hx hz
    have habs := abs_qShell_of_mem R x hx
    rw [hz] at habs
    norm_num at habs

/-- Pointwise product support equals the actual box intersection. -/
theorem familyProduct_ne_zero_iff (S : Finset (Shape d h)) (c : Family S) (x : Tusnady.Point d) :
    familyProduct S c x ≠ 0 ↔ ∀ r : S, x ∈ shellBox (familyShell S c r) := by
  classical
  unfold familyProduct
  simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, true_imp_iff, qShell_ne_zero_iff]

/-- Compatibility is exactly nonvanishing of the actual Walsh product
somewhere; it is not an independent geometric premise. -/
theorem compatible_iff_product_nonzero (S : Finset (Shape d h)) (c : Family S) :
    Compatible S c ↔ ∃ x, familyProduct S c x ≠ 0 := by
  simp only [Compatible, familyProduct_ne_zero_iff]

/-- A concrete real point in a join cell (its lower corner). -/
def joinCellPoint (S : Finset (Shape d h)) (I : CellIndices (join S)) : Tusnady.Point d :=
  fun k => dyadicLeft (join S k) (I k)

lemma joinCellPoint_mem (S : Finset (Shape d h)) (I : CellIndices (join S)) (k : Fin d) :
    joinCellPoint S I k ∈ dyadicInterval (join S k) (I k) := by
  constructor
  · exact le_rfl
  · change dyadicLeft (join S k) (I k) < dyadicLeft (join S k) (I k)+dyadicLength (join S k)
    linarith [dyadicLength_pos (join S k)]

/-- Every ancestor family has a genuine common real point. -/
theorem ancestorFamily_compatible (S : Finset (Shape d h)) (I : CellIndices (join S)) :
    Compatible S (boxFamilyFromCell S I) := by
  refine ⟨joinCellPoint S I, ?_⟩
  intro r k
  exact dyadicInterval_subset_ancestor (depth_le_join S r.property k) (I k) (joinCellPoint_mem S I k)

/-- Every compatible real family is the ancestor family of a join cell.
The proof reconstructs that cell from a common real point and uses the
proved uniqueness of actual dyadic intervals. -/
theorem compatible_mem_range (S : Finset (Shape d h)) (hS : S.Nonempty) (c : Family S)
    (hc : Compatible S c) : c ∈ Set.range (boxFamilyFromCell S) := by
  classical
  obtain ⟨x,hx⟩ := hc
  obtain ⟨r₀,hr₀⟩ := hS
  have hunit : ∀ k, x k ∈ Ico (0:ℝ) 1 :=
    shellBox_subset_cube (familyShell S c ⟨r₀,hr₀⟩) (hx ⟨r₀,hr₀⟩)
  let I : CellIndices (join S) := fun k =>
    Classical.choose (existsUnique_unit_interval (join S k) (x k) (hunit k))
  have hI : ∀ k, x k ∈ dyadicInterval (join S k) (I k) := fun k =>
    (Classical.choose_spec (existsUnique_unit_interval (join S k) (x k) (hunit k))).1
  refine ⟨I, ?_⟩
  funext r k
  have hanc := dyadicInterval_subset_ancestor (depth_le_join S r.property k) (I k) (hI k)
  by_contra hne
  exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth (r.val.depth k) _ _ hne)) hanc (hx r k)

/-- Actual real compatibility equals the concrete ancestor-family range. -/
theorem compatible_iff_range (S : Finset (Shape d h)) (hS : S.Nonempty) (c : Family S) :
    Compatible S c ↔ c ∈ Set.range (boxFamilyFromCell S) := by
  constructor
  · exact compatible_mem_range S hS c
  · rintro ⟨I,rfl⟩
    exact ancestorFamily_compatible S I

instance compatibleFamily_fintype (S : Finset (Shape d h)) : Fintype {c : Family S // Compatible S c} := by
  classical
  infer_instance

/-- The full real-geometric bijection in Manuscript Lemma 4.2(a). -/
def familyCellEquiv (S : Finset (Shape d h)) (hS : S.Nonempty) :
    CellIndices (join S) ≃ {c : Family S // Compatible S c} :=
  Equiv.ofBijective (fun I => ⟨boxFamilyFromCell S I,ancestorFamily_compatible S I⟩)
    ⟨fun I J h => boxFamilyFromCell_injective S hS (congrArg Subtype.val h), by
      intro c
      obtain ⟨I,hI⟩ := compatible_mem_range S hS c.val c.property
      exact ⟨I,Subtype.ext hI⟩⟩

/-- Exactly 2^(h+e) compatible/nonzero-product families, now for the actual
real shell boxes rather than only a formal range definition. -/
theorem card_compatibleFamilies (S : Finset (Shape d h)) (hS : S.Nonempty) :
    Fintype.card {c : Family S // Compatible S c} = 2^(h+excess S) := by
  rw [← Fintype.card_congr (familyCellEquiv S hS), card_joinCells S hS]

end Tusnady.Cell
