/-
Adapted from Per Alexandersson et al., RealRooted.
Source: https://github.com/PerAlexandersson/RealRooted
Revision: 5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837
Original path: RealRooted/Mathlib/Algebra/MvPolynomial/PDeriv.lean
License: Apache-2.0 (see LICENSE in this directory tree).
Ported to Lean/mathlib 4.24 without changing theorem premises.
-/
/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Partial derivatives of squarefree monomials
-/


open scoped BigOperators

namespace MvPolynomial

/-- The earlier left-multiplication coefficient formula, derived from the
now-native mathlib coefficient theorem. -/
theorem coeff_pderiv_left {R σ : Type*} [CommSemiring R] (i : σ)
    (P : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (pderiv i P).coeff m = ((m i + 1 : ℕ) : R) * P.coeff (m + Finsupp.single i 1) := by
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using (MvPolynomial.coeff_pderiv (i := i) P m)

/-- The partial derivative of a numeral constant is zero. -/
@[simp] theorem pderiv_ofNat {R σ : Type*} [CommSemiring R]
    (i : σ) (n : Nat) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : MvPolynomial σ R) = 0 := by
  rw [← map_ofNat (C : R →+* MvPolynomial σ R) n]
  exact pderiv_C

/-- Differentiate a squarefree monomial presented as a finite product of
variables. -/
theorem pderiv_finsetProd_X {R σ : Type*} [CommSemiring R] [DecidableEq σ]
    (x : σ) (t : Finset σ) :
    pderiv x (∏ y ∈ t, X y : MvPolynomial σ R) =
      if x ∈ t then ∏ y ∈ t.erase x, X y else 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      by_cases hax : a = x
      · subst a
        simp [ha, ih]
      · have hxa : x ≠ a := Ne.symm hax
        by_cases hxt : x ∈ t
        · have haerase : a ∉ t.erase x := fun h => ha (Finset.erase_subset x t h)
          simp [ha, hax, hxa, hxt, ih, Finset.erase_insert_of_ne hax, haerase]
        · simp [ha, hax, hxa, hxt, ih]

open scoped Classical in
/-- The partial derivative of a possibly noninjective renaming is the sum of
the renamed partial derivatives over the corresponding source fiber. -/
theorem pderiv_rename_eq_sum_fiber {R σ τ : Type*} [CommSemiring R] [Fintype σ]
    (f : σ → τ) (j : τ) (P : MvPolynomial σ R) :
    pderiv j (rename f P) =
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), rename f (pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, Finset.sum_add_distrib]
  | mul_X P x hP =>
      simp only [map_mul, rename_X, pderiv_mul, hP, map_add, pderiv_X,
        Pi.single_apply]
      by_cases hx : f x = j <;>
        simp [hx, Finset.sum_add_distrib, Finset.sum_mul]

end MvPolynomial
