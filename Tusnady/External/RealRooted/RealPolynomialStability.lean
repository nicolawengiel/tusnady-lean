/-
Adapted from RealRooted, revision 5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837,
Apache-2.0 (LICENSE in this directory). Sources: RootContinuity.lean,
HermiteBiehler/Basic.lean, Mathlib/Algebra/Polynomial/Splits/Complex.lean.
Only the splitness/stability facts required by the MSS proof are extracted.
-/
import Tusnady.External.RealRooted.PointwiseStability

noncomputable section
open Polynomial
namespace RealRooted

def complexify (p : ℝ[X]) : ℂ[X] := p.map Complex.ofRealHom

def IsUpperHalfPlaneStable (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0

theorem splits_of_forall_aeval_im_eq_zero {p : ℝ[X]}
    (h : ∀ z : ℂ, p.aeval z = 0 → z.im = 0) :
    p.Splits (RingHom.id ℝ) := by
  apply Polynomial.splits_id_of_splits Complex.ofRealHom (IsAlgClosed.splits_codomain _)
  intro z hz
  refine ⟨z.re, ?_⟩
  have heval : p.aeval z = 0 := by
    simpa only [Polynomial.aeval_def, ← Polynomial.eval_map] using
      Polynomial.isRoot_of_mem_roots hz
  exact Complex.ext (by simp) (by simpa using (h z heval).symm)

theorem im_eq_zero_of_aeval_eq_zero {p : ℝ[X]} (hp : p ≠ 0)
    (hs : p.Splits (RingHom.id ℝ)) {z : ℂ} (hz : p.aeval z = 0) : z.im = 0 := by
  have hm : z ∈ (p.map Complex.ofRealHom).roots := by
    apply (Polynomial.mem_roots (Polynomial.map_ne_zero hp)).mpr
    simpa only [Polynomial.aeval_def, ← Polynomial.eval_map] using hz
  rw [Polynomial.roots_map Complex.ofRealHom hs] at hm
  obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hm
  simp

theorem eval_complexify_eq_prod {p : ℝ[X]} (hp : p.Splits (RingHom.id ℝ)) {z : ℂ} :
    (complexify p).eval z = (p.leadingCoeff : ℂ) *
      (p.roots.map (fun r : ℝ => z - (r : ℂ))).prod :=
  eval_map_ofReal_eq_prod hp

theorem eval_complexify_ne_zero_of_splits_of_im_pos {p : ℝ[X]}
    (hp : p.Splits (RingHom.id ℝ)) (hp₀ : p ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    (complexify p).eval z ≠ 0 := by
  rw [eval_complexify_eq_prod hp]
  refine mul_ne_zero (by simp [hp₀]) ?_
  apply Multiset.prod_ne_zero
  simp only [Multiset.mem_map, not_exists, not_and]
  rintro r _ heq
  exact hz.ne' (by simpa using congrArg Complex.im heq)

theorem eval_complexify_conj (f : ℝ[X]) (z : ℂ) :
    (complexify f).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((complexify f).eval z) := by
  have h : (starRingEnd ℂ).comp Complex.ofRealHom = Complex.ofRealHom := by
    ext x
    simp
  simp [complexify, eval_map, hom_eval₂, h]

theorem complexify_conj_root {f : ℝ[X]} {z : ℂ}
    (hz : (complexify f).eval z = 0) :
    (complexify f).eval (starRingEnd ℂ z) = 0 := by
  rw [eval_complexify_conj, hz, map_zero]

theorem IsUpperHalfPlaneStable.splits_complexify {p : ℝ[X]}
    (hp : IsUpperHalfPlaneStable (complexify p)) : p.Splits (RingHom.id ℝ) := by
  apply splits_of_forall_aeval_im_eq_zero
  intro z hz
  have hz' : (complexify p).eval z = 0 := by
    simpa only [complexify, Polynomial.aeval_def, ← Polynomial.eval_map] using hz
  rcases lt_trichotomy z.im 0 with h | h | h
  · exact False.elim ((hp _ (by simpa using h)) (complexify_conj_root hz'))
  · exact h
  · exact False.elim ((hp z h) hz')

end RealRooted
