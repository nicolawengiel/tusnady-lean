import Tusnady.DyadicIntervals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Concrete localized Walsh functions on the base interval

Functions and integrals in this file are actual real functions and Lebesgue
Bochner integrals. The eight half-open pieces have signs
`(+,-,-,+,-,+,+,-)`, as in Manuscript Lemma 2.2.
-/

set_option autoImplicit false

noncomputable section

namespace Tusnady.DyadicFunctions

open MeasureTheory Set
open scoped BigOperators

/-- Left endpoint of the `i`th eighth of the unit interval. -/
def cellLo (i : Fin 8) : ℝ := (i.val : ℝ) / 8

/-- Right endpoint of the `i`th eighth of the unit interval. -/
def cellHi (i : Fin 8) : ℝ := ((i.val : ℝ) + 1) / 8

def baseCell (i : Fin 8) : Set ℝ := Ico (cellLo i) (cellHi i)

/-- Three-bit Walsh sign pattern. -/
def walshSign : Fin 8 → ℝ := ![1, -1, -1, 1, -1, 1, 1, -1]

/-- A function restricted to one actual half-open eighth-cell. -/
def patch (i : Fin 8) (f : ℝ → ℝ) : ℝ → ℝ := (baseCell i).indicator f

/-- The concrete three-bit Walsh function, zero outside `[0,1)`. -/
def qBase (x : ℝ) : ℝ := ∑ i : Fin 8, patch i (fun _ => walshSign i) x

/-- Intercepts of the eight affine primitive pieces. -/
def primitiveIntercept : Fin 8 → ℝ := ![0, -(1/4), -(1/4), 1/2, -(1/2), 3/4, 3/4, -1]

/-- The affine expression for the primitive on one eighth-cell. -/
def primitivePiece (i : Fin 8) (x : ℝ) : ℝ := -walshSign i * x + primitiveIntercept i

/-- Explicit candidate for the primitive, defined as actual affine patches. -/
def psiBase (x : ℝ) : ℝ := ∑ i : Fin 8, patch i (primitivePiece i) x

lemma cellLo_le_cellHi (i : Fin 8) : cellLo i ≤ cellHi i := by
  unfold cellLo cellHi
  linarith

lemma baseCell_disjoint {i j : Fin 8} (hij : i ≠ j) : Disjoint (baseCell i) (baseCell j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  change cellLo i ≤ x ∧ x < cellHi i at hx
  change cellLo j ≤ x ∧ x < cellHi j at hy
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with h | h
  · have hstep : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast h
    unfold cellLo cellHi at hx hy
    linarith
  · have hstep : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast h
    unfold cellLo cellHi at hx hy
    linarith

lemma patch_integrable (i : Fin 8) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable (patch i f) := by
  unfold patch baseCell
  rw [integrable_indicator_iff measurableSet_Ico]
  exact hf.integrableOn_Icc.mono_set Ico_subset_Icc_self

lemma integral_patch (i : Fin 8) (f : ℝ → ℝ) :
    (∫ x, patch i f x) = ∫ x in cellLo i..cellHi i, f x := by
  rw [patch, baseCell, integral_indicator measurableSet_Ico, ← integral_Icc_eq_integral_Ico,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (cellLo_le_cellHi i)]

lemma patch_mul (i : Fin 8) (f g : ℝ → ℝ) (x : ℝ) :
    patch i f x * g x = patch i (fun y => f y * g y) x := by
  by_cases hx : x ∈ baseCell i <;> simp [patch, hx]

lemma patch_sum_eval (F : Fin 8 → ℝ → ℝ) (i : Fin 8) (x : ℝ) (hx : x ∈ baseCell i) :
    (∑ j : Fin 8, patch j (F j) x) = F i x := by
  rw [Finset.sum_eq_single i]
  · simp [patch, hx]
  · intro j _ hji
    have hnot : x ∉ baseCell j := by
      intro hxj
      exact (Set.disjoint_left.mp (baseCell_disjoint hji)) hxj hx
    simp [patch, hnot]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

lemma patch_sum_zero (F : Fin 8 → ℝ → ℝ) (x : ℝ)
    (hx : ∀ i : Fin 8, x ∉ baseCell i) : (∑ i : Fin 8, patch i (F i) x) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  simp [patch, hx i]

lemma square_patch_sum (F : Fin 8 → ℝ → ℝ) (x : ℝ) :
    (∑ i : Fin 8, patch i (F i) x) ^ 2 =
      ∑ i : Fin 8, patch i (fun y => F i y ^ 2) x := by
  classical
  by_cases hx : ∃ i : Fin 8, x ∈ baseCell i
  · obtain ⟨i, hi⟩ := hx
    rw [patch_sum_eval F i x hi, patch_sum_eval (fun j y => F j y ^ 2) i x hi]
  · have hnone : ∀ i : Fin 8, x ∉ baseCell i := by simpa only [not_exists] using hx
    rw [patch_sum_zero F x hnone, patch_sum_zero (fun j y => F j y ^ 2) x hnone]
    norm_num

/-- Exact moment formula, obtained from eight actual integrals. -/
theorem qBase_moment_formula (n : ℕ) :
    (∫ x, qBase x * x ^ n) =
      ∑ i : Fin 8, walshSign i *
        ((cellHi i ^ (n+1) - cellLo i ^ (n+1)) / (n+1)) := by
  have hfun : (fun x => qBase x * x ^ n) =
      (fun x => ∑ i : Fin 8, patch i (fun x => walshSign i * x ^ n) x) := by
    funext x
    unfold qBase
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact patch_mul i (fun _ => walshSign i) (fun y => y ^ n) x
  rw [hfun, integral_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_patch, intervalIntegral.integral_const_mul, integral_pow]
  · intro i _
    exact patch_integrable i _ (by fun_prop)

/-- Zeroth moment: the localized Walsh function has mean zero. -/
theorem integral_qBase : (∫ x, qBase x) = 0 := by
  have h := qBase_moment_formula 0
  norm_num [Fin.sum_univ_succ, walshSign, cellLo, cellHi] at h
  exact h

/-- First vanishing moment. -/
theorem integral_qBase_mul_id : (∫ x, qBase x * x) = 0 := by
  have h := qBase_moment_formula 1
  norm_num [Fin.sum_univ_succ, walshSign, cellLo, cellHi] at h
  exact h

/-- Second vanishing moment. -/
theorem integral_qBase_mul_sq : (∫ x, qBase x * x ^ 2) = 0 := by
  have h := qBase_moment_formula 2
  norm_num [Fin.sum_univ_succ, walshSign, cellLo, cellHi] at h
  exact h

lemma integral_affine_mul_pow (a b l u : ℝ) (n : ℕ) :
    (∫ x in l..u, (a*x+b) * x^n) =
      a * ((u^(n+2)-l^(n+2))/(n+2)) + b * ((u^(n+1)-l^(n+1))/(n+1)) := by
  have hfun : (fun x : ℝ => (a*x+b) * x^n) =
      (fun x => a*x^(n+1) + b*x^n) := by
    funext x
    rw [pow_succ]
    ring
  rw [hfun, intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_pow, integral_pow]
    push_cast
    ring
  · exact (by fun_prop : Continuous (fun x : ℝ => a*x^(n+1))).intervalIntegrable _ _
  · exact (by fun_prop : Continuous (fun x : ℝ => b*x^n)).intervalIntegrable _ _

/-- Exact moments of the explicit primitive pieces. -/
theorem psiBase_moment_formula (n : ℕ) :
    (∫ x, psiBase x * x ^ n) = ∑ i : Fin 8,
      ((-walshSign i) * ((cellHi i^(n+2)-cellLo i^(n+2))/(n+2)) +
        primitiveIntercept i * ((cellHi i^(n+1)-cellLo i^(n+1))/(n+1))) := by
  have hfun : (fun x => psiBase x * x ^ n) =
      (fun x => ∑ i : Fin 8, patch i (fun x => primitivePiece i x * x ^ n) x) := by
    funext x
    unfold psiBase
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact patch_mul i (primitivePiece i) (fun y => y ^ n) x
  rw [hfun, integral_finset_sum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_patch]
    exact integral_affine_mul_pow (-walshSign i) (primitiveIntercept i) _ _ n
  · intro i _
    exact patch_integrable i _ (by unfold primitivePiece; fun_prop)

/-- The primitive has mean zero. -/
theorem integral_psiBase : (∫ x, psiBase x) = 0 := by
  have h := psiBase_moment_formula 0
  norm_num [Fin.sum_univ_succ, walshSign, primitiveIntercept, cellLo, cellHi] at h
  exact h

/-- The primitive has first moment zero. -/
theorem integral_psiBase_mul_id : (∫ x, psiBase x * x) = 0 := by
  have h := psiBase_moment_formula 1
  norm_num [Fin.sum_univ_succ, walshSign, primitiveIntercept, cellLo, cellHi] at h
  exact h

lemma integral_affine_sq (a b l u : ℝ) :
    (∫ x in l..u, (a*x+b)^2) =
      a^2*((u^3-l^3)/3) + (2*a*b)*((u^2-l^2)/2) + b^2*(u-l) := by
  have hfun : (fun x : ℝ => (a*x+b)^2) =
      (fun x => (a^2*x^2 + (2*a*b)*x) + b^2) := by
    funext x
    ring
  have h₁ : IntervalIntegrable (fun x : ℝ => a^2*x^2) volume l u :=
    (by fun_prop : Continuous (fun x : ℝ => a^2*x^2)).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun x : ℝ => (2*a*b)*x) volume l u :=
    (by fun_prop : Continuous (fun x : ℝ => (2*a*b)*x)).intervalIntegrable _ _
  have h₃ : IntervalIntegrable (fun _ : ℝ => b^2) volume l u := intervalIntegrable_const
  rw [hfun, intervalIntegral.integral_add (h₁.add h₂) h₃,
    intervalIntegral.integral_add h₁ h₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_pow, integral_id,
    intervalIntegral.integral_const]
  simp only [Nat.reduceAdd, Nat.cast_ofNat, smul_eq_mul]
  ring

/-- Exact squared L² integral of the explicit primitive on the real line. -/
theorem integral_psiBase_sq : (∫ x, psiBase x ^ 2) = (1 : ℝ) / 192 := by
  have hfun : (fun x => psiBase x ^ 2) =
      (fun x => ∑ i : Fin 8, patch i (fun x => primitivePiece i x ^ 2) x) := by
    funext x
    exact square_patch_sum primitivePiece x
  rw [hfun, integral_finset_sum Finset.univ]
  · simp_rw [integral_patch]
    simp only [primitivePiece]
    simp_rw [integral_affine_sq]
    norm_num [Fin.sum_univ_succ, walshSign, primitiveIntercept, cellLo, cellHi]
  · intro i _
    exact patch_integrable i _ (by unfold primitivePiece; fun_prop)

end Tusnady.DyadicFunctions
