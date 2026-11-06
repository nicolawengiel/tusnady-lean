/-
Adapted from RealRooted, revision 5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837.
Original path: RealRooted/Mathlib/RingTheory/MvPolynomial/Homogeneous.lean
Apache-2.0; see LICENSE in this directory tree.
-/
/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Extensions to homogeneous multivariate polynomials

This file contains results intended for upstreaming to
`Mathlib.RingTheory.MvPolynomial.Homogeneous`.
-/



namespace MvPolynomial

-- `IsHomogeneous.degree_eq_sum_deg_support` is now native in mathlib.

/-- The homogeneous component in the total degree of a nonzero polynomial is
nonzero. -/
theorem homogeneousComponent_totalDegree_ne_zero
    {σ R : Type*} [CommSemiring R] {P : MvPolynomial σ R} (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  obtain ⟨m, hm, hdegree⟩ := Finset.exists_mem_eq_sup P.support
    (MvPolynomial.support_nonempty.mpr hP) (fun d => d.degree)
  have htotal : P.totalDegree = m.degree := by
    have hfun :
        (fun s : σ →₀ ℕ => s.sum fun _ e => e) =
          fun s => s.degree := by
      funext s
      rfl
    rw [MvPolynomial.totalDegree, hfun]
    exact hdegree
  intro hzero
  have hcoeff : (homogeneousComponent P.totalDegree P).coeff m = (0 : MvPolynomial σ R).coeff m :=
    congrArg (fun Q : MvPolynomial σ R => Q.coeff m) hzero
  rw [MvPolynomial.coeff_homogeneousComponent, if_pos htotal.symm] at hcoeff
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hm) hcoeff

end MvPolynomial
