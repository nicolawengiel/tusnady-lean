import Tusnady.CellFamilyL2

/-!
# Shape-distinct shell sets and the actual cell structure

This interface accepts finite sets of actual shells, as occur in the
squarefree expansion of W. Distinctness of shapes is checked explicitly.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.Dyadic Tusnady.DyadicFunctions Tusnady.Haar Tusnady.Witness
open scoped BigOperators
variable {d h : ℕ}

def shapeSet (Γ : Finset (Shell d h)) : Finset (Shape d h) := Γ.image Sigma.fst

def DistinctShapes (Γ : Finset (Shell d h)) : Prop := Set.InjOn Sigma.fst (Γ : Set (Shell d h))

lemma exists_cell_of_shape (Γ : Finset (Shell d h)) (r : shapeSet Γ) :
    ∃ c : CellIndices r.val.depth, (⟨r.val,c⟩ : Shell d h) ∈ Γ := by
  classical
  obtain ⟨⟨s,c⟩,hmem,hs⟩ := Finset.mem_image.mp r.property
  cases hs
  exact ⟨c,hmem⟩

def familyOfShellSet (Γ : Finset (Shell d h)) : Family (shapeSet Γ) :=
  fun r => Classical.choose (exists_cell_of_shape Γ r)

lemma familyOfShellSet_mem (Γ : Finset (Shell d h)) (r : shapeSet Γ) :
    familyShell (shapeSet Γ) (familyOfShellSet Γ) r ∈ Γ :=
  Classical.choose_spec (exists_cell_of_shape Γ r)

def shellSetShapeEquiv (Γ : Finset (Shell d h)) (hΓ : DistinctShapes Γ) : shapeSet Γ ≃ Γ :=
  Equiv.ofBijective (fun r => ⟨familyShell (shapeSet Γ) (familyOfShellSet Γ) r,familyOfShellSet_mem Γ r⟩)
    ⟨by
      intro r s hrs
      apply Subtype.ext
      exact congrArg Sigma.fst (congrArg Subtype.val hrs), by
      intro R
      let r : shapeSet Γ := ⟨R.val.1,Finset.mem_image.mpr ⟨R.val,R.property,rfl⟩⟩
      refine ⟨r,Subtype.ext ?_⟩
      apply hΓ (familyOfShellSet_mem Γ r) R.property
      rfl⟩

/-- Actual squarefree product equals its one-shell-per-shape family
representation; this does not introduce a decomposition premise. -/
theorem shellSet_product_eq_family (Γ : Finset (Shell d h)) (hΓ : DistinctShapes Γ)
    (x : Tusnady.Point d) :
    (∏ R ∈ Γ, qShell R x) = familyProduct (shapeSet Γ) (familyOfShellSet Γ) x := by
  classical
  rw [← Finset.prod_coe_sort Γ]
  exact ((shellSetShapeEquiv Γ hΓ).prod_comp (fun R => qShell R.val x)).symm

lemma shapeSet_nonempty (Γ : Finset (Shell d h)) (hΓ : Γ.Nonempty) : (shapeSet Γ).Nonempty :=
  hΓ.image Sigma.fst

/-- Lemma 4.2(b) directly for an actual shape-distinct shell set whose
product is nonzero somewhere. Both the cell and the sign are constructed
from the actual boxes; the identity holds globally on real space. -/
theorem shellSet_cell_structure (Γ : Finset (Shell d h)) (hΓ : DistinctShapes Γ)
    (hne : Γ.Nonempty) (hnz : ∃ x, (∏ R ∈ Γ, qShell R x) ≠ 0) :
    ∃ I : CellIndices (join (shapeSet Γ)), ∃ σ : ℝ, |σ| = 1 ∧
      ∀ x, (∏ R ∈ Γ, qShell R x) =
        σ*cellValue (join (shapeSet Γ)) I (peakModulated (shapeSet Γ)) x := by
  classical
  have hS := shapeSet_nonempty Γ hne
  have hc : Compatible (shapeSet Γ) (familyOfShellSet Γ) := by
    apply (compatible_iff_product_nonzero _ _).2
    simpa only [shellSet_product_eq_family Γ hΓ] using hnz
  obtain ⟨I,hI⟩ := compatible_mem_range (shapeSet Γ) hS (familyOfShellSet Γ) hc
  refine ⟨I,cellSign (shapeSet Γ) I,cellSign_abs _ _,?_⟩
  intro x
  rw [shellSet_product_eq_family Γ hΓ, ← hI]
  exact familyProduct_factorization _ hS I x

end Tusnady.Cell
