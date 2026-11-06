/-
Adapted from Per Alexandersson et al., RealRooted.
Source: https://github.com/PerAlexandersson/RealRooted
Revision: 5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837
Original path: RealRooted/Mathlib/Analysis/Complex/Polynomial/ClosedRoots/Real.lean
License: Apache-2.0 (see LICENSE in this directory tree).
Ported to Lean/mathlib 4.24 without changing theorem premises.
-/
/-
Copyright (c) 2026 Per Alexandersson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Per Alexandersson
-/

import Tusnady.External.RealRooted.RealPolynomialStability
import Tusnady.External.RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Splits

/-!
# Limits of real-rooted polynomials

Pointwise limits (on `ℂ`) of real polynomials that are zero or split, with uniformly bounded
degree, are again zero or split. The proof applies the closed-root-set result of
`RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots` to the closed set `{z | z.im = 0}`
and `Polynomial.splits_of_all_roots_real`.

## Main statements

* `Polynomial.eq_zero_or_splits_of_tendsto_eval_of_natDegree_le`: if `p n` is zero or splits,
  `(p n).natDegree ≤ N`, and the complexified evaluations converge pointwise to those of `p₀`,
  then `p₀ = 0 ∨ p₀.Splits`.
-/


noncomputable section

open Filter Topology

namespace Polynomial

/-- Pointwise limits of real splitting polynomials with uniformly bounded
degree are zero or split. -/
theorem eq_zero_or_splits_of_tendsto_eval_of_natDegree_le
    {p : ℕ → ℝ[X]} {p₀ : ℝ[X]} {N : ℕ}
    (hdeg : ∀ n, (p n).natDegree ≤ N)
    (hsplit : ∀ n, p n = 0 ∨ (p n).Splits)
    (heval : ∀ z : ℂ, Tendsto
      (fun n => ((p n).map Complex.ofRealHom).eval z) atTop
        (𝓝 ((p₀.map Complex.ofRealHom).eval z))) :
    p₀ = 0 ∨ p₀.Splits := by
  by_cases hp₀ : p₀ = 0
  · exact Or.inl hp₀
  right
  apply RealRooted.splits_of_forall_aeval_im_eq_zero
  intro z hz
  have hzroots : z ∈ (p₀.map Complex.ofRealHom).roots :=
    (mem_roots (Polynomial.map_ne_zero hp₀)).mpr (by
      have hmap : Complex.ofRealHom = algebraMap ℝ ℂ := by ext x; rfl
      simpa only [Polynomial.IsRoot, Polynomial.aeval_def, ← Polynomial.eval_map, ← hmap] using hz)
  have hreal : z ∈ {z : ℂ | z.im = 0} :=
    roots_mem_of_tendsto_eval_of_natDegree_le
      (isClosed_eq Complex.continuous_im continuous_const)
      (fun n => by
        simpa only [natDegree_map_eq_of_injective Complex.ofRealHom.injective] using hdeg n)
      (fun n r hr => by
        rcases hsplit n with hpzero | hpsplits
        · rw [hpzero] at hr
          simp at hr
        · rw [hpsplits.roots_map Complex.ofRealHom, Multiset.mem_map] at hr
          obtain ⟨s, -, rfl⟩ := hr
          simp)
      heval z hzroots
  exact hreal

end Polynomial
