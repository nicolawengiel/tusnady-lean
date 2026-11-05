import Mathlib.Algebra.MvPolynomial.Equiv

/-!
Compatibility with the later generic unique-variable equivalence.
Constructed from the pinned mathlib's proved PUnit equivalence and renaming.
No later mathlib result or unproved assumption is imported.
-/
noncomputable section
namespace MvPolynomial

variable (R : Type*) [CommSemiring R] (ι : Type*) [Unique ι]

def uniqueAlgEquiv : MvPolynomial ι R ≃ₐ[R] Polynomial R :=
  (renameEquiv R (Equiv.equivPUnit ι : ι ≃ PUnit.{1})).trans (pUnitAlgEquiv R)

variable {R ι}

theorem eval₂_const_uniqueAlgEquiv {S : Type*} [CommSemiring S]
    {f : MvPolynomial ι R} {φ : R →+* S} {a : S} :
    ((uniqueAlgEquiv R ι) f).eval₂ φ a = f.eval₂ φ (fun _ => a) := by
  simp only [uniqueAlgEquiv, AlgEquiv.trans_apply, eval₂_const_pUnitAlgEquiv,
    renameEquiv_apply, eval₂_rename, Function.comp_def]

end MvPolynomial
