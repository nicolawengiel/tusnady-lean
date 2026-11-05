import Tusnady.HaarPrimitives
import Tusnady.HaarExpansion

/-! # Actual integral orthogonality for the finite Haar construction. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators

/-- An interval indicator is constant on each finer dyadic interval. -/
theorem indicatorI_on_finer (a b : ℕ) (hab : a ≤ b) (i : Fin (2^a)) (j : Fin (2^b))
    (x : ℝ) (hx : x ∈ dyadicInterval b j) :
    indicatorI a i x =
      if Tusnady.Dyadic.ancestorIndex j a hab = i then 1 else 0 := by
  classical
  by_cases heq : Tusnady.Dyadic.ancestorIndex j a hab = i
  · rw [if_pos heq]
    have hsub := dyadicInterval_subset_ancestor hab j
    rw [heq] at hsub
    exact Set.indicator_of_mem (hsub hx) (fun _ : ℝ => (1:ℝ))
  · rw [if_neg heq]
    have hnot : x ∉ dyadicInterval a i := by
      intro hxi
      exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a _ i heq))
        (dyadicInterval_subset_ancestor hab j hx) hxi
    exact Set.indicator_of_notMem hnot (fun _ : ℝ => (1:ℝ))

/-- Haar functions are constant at every depth at least one level finer. -/
theorem hI_constant_on_finer (a b : ℕ) (hab : a+1 ≤ b) (i : Fin (2^a)) (j : Fin (2^b)) :
    ∃ value : ℝ, EqOn (hI a i) (fun _ => value) (dyadicInterval b j) := by
  classical
  refine ⟨(if Tusnady.Dyadic.ancestorIndex j (a+1) hab = refineIndex a 1 i 0 then 1 else 0) -
    (if Tusnady.Dyadic.ancestorIndex j (a+1) hab = refineIndex a 1 i 1 then 1 else 0), ?_⟩
  intro x hx
  unfold hI
  rw [indicatorI_on_finer _ _ hab _ _ x hx, indicatorI_on_finer _ _ hab _ _ x hx]

lemma abs_rademacher (j : ℕ) (x : ℝ) : |rademacher j x| = 1 := by
  unfold rademacher
  rw [abs_pow]
  norm_num

/-- Exact pointwise Haar absolute value. -/
theorem abs_hI (a : ℕ) (i : Fin (2^a)) (x : ℝ) : |hI a i x| = indicatorI a i x := by
  rw [hI_eq_rademacher]
  by_cases hx : x ∈ dyadicInterval a i
  · rw [Set.indicator_of_mem hx]
    rw [abs_rademacher]
    exact (Set.indicator_of_mem hx (fun _ : ℝ => (1:ℝ))).symm
  · rw [Set.indicator_of_notMem hx]
    unfold indicatorI
    rw [Set.indicator_of_notMem hx]
    norm_num

lemma integral_indicatorI (a : ℕ) (i : Fin (2^a)) :
    (∫ x, indicatorI a i x) = dyadicLength a := by
  have hfun : (fun x => indicatorI a i x) = (fun x => |qI a i x|) := by
    funext x
    exact (abs_q (dyadicLeft a i) (dyadicLength a) x (dyadicLength_pos a)).symm
  rw [hfun]
  exact integral_abs_qI a i

/-- Actual squared norm of a real Haar function. -/
theorem integral_hI_sq (a : ℕ) (i : Fin (2^a)) :
    (∫ x, hI a i x^2) = dyadicLength a := by
  have hfun : (fun x => hI a i x^2) = indicatorI a i := by
    funext x
    rw [← sq_abs, abs_hI]
    by_cases hx : x ∈ dyadicInterval a i <;> simp [indicatorI, hx]
  rw [hfun]
  exact integral_indicatorI a i

lemma integral_unit_hI (a : ℕ) (i : Fin (2^a)) :
    (∫ x in (0:ℝ)..1, hI a i x) = 0 := by
  rw [integral_unit_eq_global]
  · exact integral_hI a i
  · intro x hx
    exact hI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h))

lemma integral_unit_hI_sq (a : ℕ) (i : Fin (2^a)) :
    (∫ x in (0:ℝ)..1, hI a i x^2) = dyadicLength a := by
  rw [integral_unit_eq_global]
  · exact integral_hI_sq a i
  · intro x hx
    rw [hI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h)), zero_pow (by omega)]

/-- Orthogonality at different Haar depths, using exact constancy on the
fine support and the mean-zero integral. -/
theorem integral_unit_hI_mul_hI_separated (a b : ℕ) (hab : a+1 ≤ b)
    (i : Fin (2^a)) (j : Fin (2^b)) :
    (∫ x in (0:ℝ)..1, hI a i x*hI b j x) = 0 := by
  obtain ⟨value, hvalue⟩ := hI_constant_on_finer a b hab i j
  have hfun : (fun x => hI a i x*hI b j x) = (fun x => value*hI b j x) := by
    funext x
    by_cases hx : x ∈ dyadicInterval b j
    · rw [hvalue hx]
    · rw [hI_zero_outside b j x hx]
      ring
  rw [hfun, intervalIntegral.integral_const_mul, integral_unit_hI, mul_zero]

/-- Orthogonality of distinct Haar intervals at one depth. -/
theorem integral_unit_hI_mul_hI_same_depth (a : ℕ) (i j : Fin (2^a)) (hij : i ≠ j) :
    (∫ x in (0:ℝ)..1, hI a i x*hI a j x) = 0 := by
  have hfun : (fun x => hI a i x*hI a j x) = (fun _ => (0:ℝ)) := by
    funext x
    by_cases hx : x ∈ dyadicInterval a i
    · have hxj : x ∉ dyadicInterval a j := by
        intro h
        exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a i j hij)) hx h
      rw [hI_zero_outside a j x hxj, mul_zero]
    · rw [hI_zero_outside a i x hx, zero_mul]
  rw [hfun]
  simp

end Tusnady.Haar
