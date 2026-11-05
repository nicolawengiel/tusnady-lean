import Tusnady.DyadicFunctionsGeometry

/-!
# Concrete real Haar functions and finite dyadic refinements

The finite index construction is connected to actual half-open real intervals.
No completeness of an infinite Haar basis is assumed.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators

/-- The `t`th depth-`k` child of a dyadic interval of depth `a`. -/
def refineIndex (a k : ℕ) (i : Fin (2^a)) (t : Fin (2^k)) : Fin (2^(a+k)) :=
  ⟨2^k*i.val+t.val, by
    rw [pow_add]
    have hi : i.val+1 ≤ 2^a := i.isLt
    have ht : t.val < 2^k := t.isLt
    have hpos : 0 < 2^k := by positivity
    nlinarith⟩

/-- Exact real endpoints of a finite dyadic child. -/
theorem child_interval (a k : ℕ) (i : Fin (2^a)) (t : Fin (2^k)) :
    dyadicInterval (a+k) (refineIndex a k i t) =
      Ico (dyadicLeft a i+dyadicLength a*((t.val:ℝ)/(2:ℝ)^k))
        (dyadicLeft a i+dyadicLength a*(((t.val:ℝ)+1)/(2:ℝ)^k)) := by
  rw [dyadicInterval_endpoints]
  unfold refineIndex dyadicLeft dyadicLength
  push_cast
  rw [pow_add]
  congr 1 <;> field_simp
  ring

lemma normalized_mem_Ico (c length l u x : ℝ) (hl : 0 < length) :
    (x-c)/length ∈ Ico l u ↔ x ∈ Ico (c+length*l) (c+length*u) := by
  constructor
  · intro hx
    have hlo := (le_div_iff₀ hl).mp hx.1
    have hhi := (div_lt_iff₀ hl).mp hx.2
    constructor <;> nlinarith
  · intro hx
    constructor
    · apply (le_div_iff₀ hl).2
      nlinarith [hx.1]
    · apply (div_lt_iff₀ hl).2
      nlinarith [hx.2]

/-- A real dyadic interval indicator. -/
def indicatorI (a : ℕ) (i : Fin (2^a)) : ℝ → ℝ :=
  (dyadicInterval a i).indicator (fun _ => (1:ℝ))

/-- The discrete ancestor of a specified child is exactly its parent. -/
theorem ancestor_refine (a k : ℕ) (i : Fin (2^a)) (t : Fin (2^k)) :
    Tusnady.Dyadic.ancestorIndex (refineIndex a k i t) a (by omega) = i := by
  apply Fin.ext
  change (2^k*i.val+t.val)/2^((a+k)-a) = i.val
  rw [Nat.add_sub_cancel_left]
  apply Nat.div_eq_of_lt_le
  · nlinarith
  · have ht := t.isLt
    nlinarith

/-- Each real child lies in its parent. -/
theorem child_subset_parent (a k : ℕ) (i : Fin (2^a)) (t : Fin (2^k)) :
    dyadicInterval (a+k) (refineIndex a k i t) ⊆ dyadicInterval a i := by
  have h := dyadicInterval_subset_ancestor (by omega : a ≤ a+k) (refineIndex a k i t)
  rw [ancestor_refine] at h
  exact h

/-- Refinement preserves distinct child indices. -/
theorem refineIndex_injective (a k : ℕ) (i : Fin (2^a)) :
    Function.Injective (refineIndex a k i) := by
  intro s t h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 2^k*i.val+s.val = 2^k*i.val+t.val at hv
  omega

/-- The actual children cover their real parent interval. -/
theorem exists_child (a k : ℕ) (i : Fin (2^a)) (x : ℝ) (hx : x ∈ dyadicInterval a i) :
    ∃ t : Fin (2^k), x ∈ dyadicInterval (a+k) (refineIndex a k i t) := by
  let u := (x-dyadicLeft a i)/dyadicLength a
  have hu : u ∈ Ico (0:ℝ) 1 := (normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).2 hx
  have hD : (0:ℝ) < 2^k := by positivity
  have hnonneg : 0 ≤ (2:ℝ)^k*u := mul_nonneg hD.le hu.1
  have hlt : ⌊(2:ℝ)^k*u⌋₊ < 2^k := by
    apply (Nat.floor_lt hnonneg).2
    push_cast
    nlinarith [hu.2]
  let t : Fin (2^k) := ⟨⌊(2:ℝ)^k*u⌋₊, hlt⟩
  refine ⟨t, ?_⟩
  rw [child_interval]
  apply (normalized_mem_Ico _ _ _ _ _ (dyadicLength_pos a)).1
  change (t.val:ℝ)/(2:ℝ)^k ≤ u ∧ u < ((t.val:ℝ)+1)/(2:ℝ)^k
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((2:ℝ)^k*u)
  constructor
  · exact (div_le_iff₀ hD).2 (by simpa only [mul_comm] using hlo)
  · exact (lt_div_iff₀ hD).2 (by simpa only [mul_comm] using hhi)

/-- Exact partition identity, pointwise on all reals. -/
theorem indicatorI_sum_children (a k : ℕ) (i : Fin (2^a)) (x : ℝ) :
    indicatorI a i x = ∑ t : Fin (2^k), indicatorI (a+k) (refineIndex a k i t) x := by
  classical
  by_cases hx : x ∈ dyadicInterval a i
  · obtain ⟨t, ht⟩ := exists_child a k i x hx
    rw [Finset.sum_eq_single t]
    · simp [indicatorI, hx, ht]
    · intro s _ hst
      have hidx : refineIndex a k i s ≠ refineIndex a k i t :=
        fun h => hst (refineIndex_injective a k i h)
      have hs : x ∉ dyadicInterval (a+k) (refineIndex a k i s) := by
        intro h
        exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth _ _ _ hidx)) h ht
      simp [indicatorI, hs]
    · intro ht'
      exact False.elim (ht' (Finset.mem_univ t))
  · have hzero : ∀ t : Fin (2^k), x ∉ dyadicInterval (a+k) (refineIndex a k i t) :=
      fun t ht => hx (child_subset_parent a k i t ht)
    simp [indicatorI, hx, hzero]

/-- General real unit partition, including uniqueness at every dyadic boundary. -/
theorem existsUnique_unit_interval (a : ℕ) (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) :
    ∃! i : Fin (2^a), x ∈ dyadicInterval a i := by
  have hunit : dyadicInterval 0 0 = Ico (0:ℝ) 1 := by
    norm_num [dyadicInterval, dyadicLeft, dyadicLength]
  obtain ⟨t, ht⟩ := exists_child 0 a 0 x (by rw [hunit]; exact hx)
  have ht' : x ∈ dyadicInterval a t := by
    rw [dyadicInterval_endpoints] at ht ⊢
    simpa [refineIndex] using ht
  refine ⟨t, ht', ?_⟩
  intro s hs
  by_contra hst
  exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a s t hst)) hs ht'

/-- Standard Haar function: +1 on the left half, -1 on the right half. -/
def hI (a : ℕ) (i : Fin (2^a)) (x : ℝ) : ℝ :=
  indicatorI (a+1) (refineIndex a 1 i 0) x -
    indicatorI (a+1) (refineIndex a 1 i 1) x

/-- Base Haar function on the real half-open unit interval. -/
def hBase (x : ℝ) : ℝ :=
  (Ico (0:ℝ) ((2:ℝ)⁻¹)).indicator (fun _ => (1:ℝ)) x -
    (Ico ((2:ℝ)⁻¹:ℝ) 1).indicator (fun _ => (1:ℝ)) x

/-- The actual real Haar function is the affine-localized base Haar. -/
theorem hI_eq_hBase (a : ℕ) (i : Fin (2^a)) (x : ℝ) :
    hI a i x = hBase ((x-dyadicLeft a i)/dyadicLength a) := by
  unfold hI indicatorI hBase
  rw [child_interval, child_interval]
  norm_num
  have hleft := normalized_mem_Ico (dyadicLeft a i) (dyadicLength a) 0 ((2:ℝ)⁻¹) x (dyadicLength_pos a)
  have hright := normalized_mem_Ico (dyadicLeft a i) (dyadicLength a) ((2:ℝ)⁻¹) 1 x (dyadicLength_pos a)
  simp only [mul_zero, add_zero, mul_one] at hleft hright
  by_cases hx0 : (x-dyadicLeft a i)/dyadicLength a ∈ Ico (0:ℝ) ((2:ℝ)⁻¹) <;>
    by_cases hx1 : (x-dyadicLeft a i)/dyadicLength a ∈ Ico ((2:ℝ)⁻¹:ℝ) 1 <;>
      simp [hx0, hx1, hleft.symm, hright.symm]

lemma hBase_zero_outside (x : ℝ) (hx : x ∉ Ico (0:ℝ) 1) : hBase x = 0 := by
  have hl : x ∉ Ico (0:ℝ) ((2:ℝ)⁻¹) := by intro h; apply hx; constructor <;> linarith [h.1, h.2]
  have hr : x ∉ Ico ((2:ℝ)⁻¹:ℝ) 1 := by intro h; apply hx; constructor <;> linarith [h.1, h.2]
  simp [hBase, hl, hr]

lemma hBase_eq_rademacher (x : ℝ) :
    hBase x = (Ico (0:ℝ) 1).indicator (rademacher 1) x := by
  by_cases hx : x ∈ Ico (0:ℝ) 1
  · rw [Set.indicator_of_mem hx]
    by_cases hhalf : x < (2:ℝ)⁻¹
    · have hf : ⌊2*x⌋₊ = 0 := (Nat.floor_eq_iff (by linarith [hx.1])).2 ⟨by norm_num; linarith [hx.1], by norm_num; linarith⟩
      have hl : x ∈ Ico (0:ℝ) ((2:ℝ)⁻¹) := ⟨hx.1, hhalf⟩
      have hr : x ∉ Ico ((2:ℝ)⁻¹:ℝ) 1 := fun h => (not_le_of_gt hhalf) h.1
      simp [hBase, hl, hr, rademacher, hf]
    · have hf : ⌊2*x⌋₊ = 1 := (Nat.floor_eq_iff (by linarith [hx.1])).2 ⟨by norm_num; linarith, by norm_num; linarith [hx.2]⟩
      have hl : x ∉ Ico (0:ℝ) ((2:ℝ)⁻¹) := fun h => hhalf h.2
      have hr : x ∈ Ico ((2:ℝ)⁻¹:ℝ) 1 := ⟨le_of_not_gt hhalf, hx.2⟩
      simp [hBase, hl, hr, rademacher, hf]
  · rw [hBase_zero_outside x hx, Set.indicator_of_notMem hx]

/-- Identification with the global Rademacher definition of Haar. -/
theorem hI_eq_rademacher (a : ℕ) (i : Fin (2^a)) (x : ℝ) :
    hI a i x = (dyadicInterval a i).indicator (rademacher (a+1)) x := by
  rw [hI_eq_hBase, hBase_eq_rademacher]
  by_cases hx : x ∈ dyadicInterval a i
  · have hu := (normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).2 hx
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hu]
    have hlevel := rademacher_dyadic_affine a 1 i.val (by omega)
      ((x-dyadicLeft a i)/dyadicLength a) hu.1
    conv_rhs => rw [dyadic_normalized_inverse a i x]
    exact hlevel.symm
  · have hu : (x-dyadicLeft a i)/dyadicLength a ∉ Ico (0:ℝ) 1 :=
      fun h => hx ((normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).1 h)
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hu]

/-- The exact eighth-cell indicator expansion of the already constructed qI. -/
theorem qI_eighth_expansion (a : ℕ) (i : Fin (2^a)) (x : ℝ) :
    qI a i x = ∑ t : Fin 8, walshSign t * indicatorI (a+3) (refineIndex a 3 i t) x := by
  unfold qI q qBase
  apply Finset.sum_congr rfl
  intro t _
  have hchild := child_interval a 3 i t
  norm_num only [Nat.reducePow] at hchild
  have hmem := normalized_mem_Ico (dyadicLeft a i) (dyadicLength a)
    (cellLo t) (cellHi t) x (dyadicLength_pos a)
  unfold indicatorI
  rw [hchild]
  unfold patch baseCell cellLo cellHi at *
  by_cases hx : (x-dyadicLeft a i)/dyadicLength a ∈ Ico ((t.val:ℝ)/8) (((t.val:ℝ)+1)/8)
  · have hc := hmem.1 hx
    simp [hx, hc]
  · have hc : x ∉ Ico (dyadicLeft a i+dyadicLength a*((t.val:ℝ)/8))
        (dyadicLeft a i+dyadicLength a*(((t.val:ℝ)+1)/8)) := fun h => hx (hmem.2 h)
    simp [hx, hc]

lemma refine_quarter_half (a : ℕ) (i : Fin (2^a)) (t : Fin 4) (r : Fin 2) :
    refineIndex (a+2) 1 (refineIndex a 2 i t) r =
      refineIndex a 3 i (refineIndex 2 1 t r) := by
  apply Fin.ext
  simp only [refineIndex, Nat.reducePow]
  ring

/-- The precise four-Haar decomposition in Manuscript equation (2.5). -/
theorem qI_eq_four_haar (a : ℕ) (i : Fin (2^a)) (x : ℝ) :
    qI a i x = hI (a+2) (refineIndex a 2 i 0) x -
      hI (a+2) (refineIndex a 2 i 1) x -
      hI (a+2) (refineIndex a 2 i 2) x + hI (a+2) (refineIndex a 2 i 3) x := by
  rw [qI_eighth_expansion]
  unfold hI
  simp_rw [refine_quarter_half]
  norm_num [Fin.sum_univ_succ, walshSign, refineIndex]
  ring

end Tusnady.Haar
