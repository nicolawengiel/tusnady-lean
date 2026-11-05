import Tusnady.HaarPrimitives

/-!
# Actual affine regions of Haar primitives

A Haar tent is affine on each real dyadic child, and hence on every finer
real dyadic cell. Disjoint cells give the zero affine function. This is a
pointwise statement on half-open cells, with no almost-everywhere premise.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions

lemma tentI_affine_on_child (a : ℕ) (i : Fin (2^a)) (t : Fin 2) :
    ∃ A B : ℝ, EqOn (tentI a i) (fun x => A*x+B)
      (dyadicInterval (a+1) (refineIndex a 1 i t)) := by
  have hl := dyadicLength_pos a
  fin_cases t
  · refine ⟨1,-dyadicLeft a i,?_⟩
    intro x hx
    have hn : (x-dyadicLeft a i)/dyadicLength a ∈ Ico (0:ℝ) (2:ℝ)⁻¹ := by
      apply (normalized_mem_Ico _ _ _ _ _ hl).2
      rw [child_interval] at hx
      simpa only [Fin.val_zero, Nat.cast_zero, pow_one, zero_div, mul_zero, add_zero,
        zero_add, one_div] using hx
    have hr : (x-dyadicLeft a i)/dyadicLength a ∉ Ico (2:ℝ)⁻¹ 1 :=
      fun h => (not_le_of_gt hn.2) h.1
    rw [tentI, tentBase, Set.indicator_of_mem hn, Set.indicator_of_notMem hr, add_zero]
    field_simp
    ring
  · refine ⟨-1,dyadicLeft a i+dyadicLength a,?_⟩
    intro x hx
    have hn : (x-dyadicLeft a i)/dyadicLength a ∈ Ico (2:ℝ)⁻¹ 1 := by
      apply (normalized_mem_Ico _ _ _ _ _ hl).2
      rw [child_interval] at hx
      norm_num at hx ⊢
      exact hx
    have hr : (x-dyadicLeft a i)/dyadicLength a ∉ Ico (0:ℝ) (2:ℝ)⁻¹ :=
      fun h => (not_lt_of_ge hn.1) h.2
    rw [tentI, tentBase, Set.indicator_of_notMem hr, Set.indicator_of_mem hn, zero_add]
    field_simp
    ring

/-- Each actual depth-b cell is an affine region of the Haar primitive as
soon as b≥a+1. No containment assumption is required. -/
theorem tentI_affine_on_finer (a b : ℕ) (hab : a+1 ≤ b)
    (i : Fin (2^a)) (j : Fin (2^b)) :
    ∃ A B : ℝ, EqOn (tentI a i) (fun x => A*x+B) (dyadicInterval b j) := by
  classical
  let n := Tusnady.Dyadic.ancestorIndex j (a+1) hab
  have hsub : dyadicInterval b j ⊆ dyadicInterval (a+1) n :=
    dyadicInterval_subset_ancestor hab j
  let k := Tusnady.Dyadic.ancestorIndex n a (by omega : a ≤ a+1)
  have hsub' : dyadicInterval (a+1) n ⊆ dyadicInterval a k :=
    dyadicInterval_subset_ancestor (by omega) n
  by_cases hki : k = i
  · have hquot : n.val/2 = i.val := by
      have hv := congrArg Fin.val hki
      change n.val/2^((a+1)-a) = i.val at hv
      simpa only [Nat.add_sub_cancel_left, Nat.pow_one] using hv
    let t : Fin 2 := ⟨n.val%2,Nat.mod_lt _ (by omega)⟩
    have hn : n = refineIndex a 1 i t := by
      apply Fin.ext
      change n.val = 2^1*i.val+n.val%2
      have hmod := Nat.mod_add_div n.val 2
      rw [hquot] at hmod
      omega
    obtain ⟨A,B,hAB⟩ := tentI_affine_on_child a i t
    refine ⟨A,B,?_⟩
    intro x hx
    apply hAB
    rw [← hn]
    exact hsub hx
  · refine ⟨0,0,?_⟩
    intro x hx
    have hnot : x ∉ dyadicInterval a i := by
      intro hxi
      exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a k i hki))
        (hsub' (hsub hx)) hxi
    rw [tentI_zero_outside a i x hnot]
    ring

end Tusnady.Haar
