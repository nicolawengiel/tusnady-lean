import Tusnady.External.RealRooted.Mathlib.Algebra.MvPolynomial.PDeriv

/-! Partial derivatives commute, proved from the pinned coefficient formula. -/
namespace MvPolynomial

theorem pderiv_comm {R σ : Type*} [CommSemiring R] (i j : σ) (p : MvPolynomial σ R) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  · ext m
    simp [coeff_pderiv, Finsupp.add_apply, hij, Ne.symm hij,
      add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]

end MvPolynomial
