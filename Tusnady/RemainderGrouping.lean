import Tusnady.RemainderJoinActivity
import Tusnady.RemainderSeries

/-! # Actual shape-set joins and class-I fiber reindexing

Joins are computed from the actual physical shape images. The block-fiber
reindexing is injective on the actual class-I sets; no coefficient sum is
supplied as a hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
attribute [local instance] Classical.propDecidable
open Tusnady.RemainderActivity Tusnady.RemainderCounting

def shapeSetJoin (p : Fin d) (S : Finset (BlockShape p h)) : Fin d → ℕ :=
  Dyadic.join (S.image (blockShapeEquiv p))

def shapeSetExcess (p : Fin d) (S : Finset (BlockShape p h)) : ℕ :=
  Dyadic.excess (S.image (blockShapeEquiv p))

theorem shapeSetJoin_sum (p : Fin d) (S : Finset (BlockShape p h)) (hS : S.Nonempty) :
    (∑ i, shapeSetJoin p S i) = h + shapeSetExcess p S := by
  have h := Dyadic.excess_add_shell (S.image (blockShapeEquiv p)) (hS.image _)
  change shapeSetExcess p S + _ = ∑ i, shapeSetJoin p S i at h
  omega

theorem shapeSetExcess_le (p : Fin d) (S : Finset (BlockShape p h)) (hS : S.Nonempty) :
    shapeSetExcess p S ≤ (d - 1) * h :=
  Dyadic.excess_le (by have := p.isLt; omega) _ (hS.image _)

theorem shapeSet_subset_allowed_join (p : Fin d) (S : Finset (BlockShape p h)) :
    S ⊆ allowedShapeSet p (shapeSetJoin p S) := by
  intro r hr
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro i
  exact Dyadic.depth_le_join (S.image (blockShapeEquiv p))
    (Finset.mem_image.mpr ⟨r, hr, rfl⟩) i

theorem fiber_eq_empty_of_not_active (p : Fin d) (S : Finset (BlockShape p h))
    (a : BlockIndex h) (ha : a ∉ activeBlocks p S) : FiniteBlocks.fiber S a = ∅ := by
  simpa [activeBlocks] using ha

theorem fiber_injective_on_single_active (p : Fin d) (a : BlockIndex h)
    (S T : Finset (BlockShape p h)) (hS : activeBlocks p S = {a})
    (hT : activeBlocks p T = {a}) (hf : FiniteBlocks.fiber S a = FiniteBlocks.fiber T a) : S = T := by
  rw [← FiniteBlocks.assemble_fiber S, ← FiniteBlocks.assemble_fiber T]
  congr 1
  funext b
  by_cases hb : b = a
  · subst b
    exact hf
  · rw [fiber_eq_empty_of_not_active p S b (by simpa [hS] using hb),
      fiber_eq_empty_of_not_active p T b (by simpa [hT] using hb)]

theorem card_eq_fiber_of_single_active (p : Fin d) (S : Finset (BlockShape p h))
    (a : BlockIndex h) (ha : activeBlocks p S = {a}) : S.card = (FiniteBlocks.fiber S a).card := by
  rw [← sum_card_fiber S]
  apply Finset.sum_eq_single a
  · intro b _ hb
    rw [fiber_eq_empty_of_not_active p S b (by simpa [ha] using hb), Finset.card_empty]
  · simp

theorem block_label_eq_of_mem_single_active (p : Fin d) (S : Finset (BlockShape p h))
    (a : BlockIndex h) (ha : activeBlocks p S = {a}) (r : BlockShape p h) (hr : r ∈ S) : r.1 = a := by
  have hb : r.1 ∈ activeBlocks p S := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hm : r.2 ∈ FiniteBlocks.fiber S r.1 := by simpa [FiniteBlocks.fiber] using hr
    exact Finset.nonempty_iff_ne_empty.mp ⟨r.2, hm⟩
  simpa only [ha, Finset.mem_singleton] using hb

theorem shapeSetJoin_single_active_coordinate (p : Fin d) (S : Finset (BlockShape p h))
    (hS : S.Nonempty) (a : BlockIndex h) (ha : activeBlocks p S = {a}) :
    shapeSetJoin p S p = a.val.val := by
  have hdepth (r : BlockShape p h) (hr : r ∈ S) : r.2.val.depth p = a.val.val := by
    have hb := block_label_eq_of_mem_single_active p S a ha r hr
    exact r.2.property.trans (congrArg (fun b : BlockIndex h => b.val.val) hb)
  apply le_antisymm
  · apply Finset.sup_le
    intro r hr
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hr
    exact (hdepth s hs).le
  · obtain ⟨r, hr⟩ := hS
    rw [← hdepth r hr]
    exact Dyadic.depth_le_join (S.image (blockShapeEquiv p))
      (Finset.mem_image.mpr ⟨r, hr, rfl⟩) p

/-- Genuine class-I coefficient sum, reindexed injectively by the one
nonempty actual block fiber and bounded by the proved third activity. -/
theorem one_block_shape_sum_bound (p : Fin d) {theta : ℝ} (htheta : 0 ≤ theta)
    (a : BlockIndex h) (E : Finset (BlockShape p h)) (s : Finset (Finset (BlockShape p h)))
    (hs : ∀ S ∈ s, S ⊆ E ∧ activeBlocks p S = {a} ∧ 3 ≤ S.card) :
    (∑ S ∈ s, shapeCoefficient p theta S ^ 2) ≤
      (1 / 4 : ℝ) ^ 2 * theta ^ 6 * ((FiniteBlocks.fiber E a).card : ℝ) ^ 3 := by
  have himage : (∑ S ∈ s, shapeCoefficient p theta S ^ 2) =
      ∑ T ∈ s.image (fun S => FiniteBlocks.fiber S a),
        ((1 / 4 : ℝ) * Walsh.coefficient (Walsh.smoothedBlock theta) T) ^ 2 := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro S hS
      rw [shapeCoefficient_one_block p theta S a (hs S hS).2.1]
    · intro S hS T hT hf
      exact fiber_injective_on_single_active p a S T (hs S hS).2.1 (hs T hT).2.1 hf
  rw [himage]
  apply le_trans _ (one_block_third_activity p htheta a (FiniteBlocks.fiber E a))
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (fiber_subset_iff S E).mp (hs S hS).1 a,
      (card_eq_fiber_of_single_active p S a (hs S hS).2.1) ▸ (hs S hS).2.2⟩
  · intro T _ _
    positivity

theorem classI_same_join_activity_bound (k h e : ℕ) (p : Fin (k + 2))
    (j : Fin (k + 2) → ℕ) (hj : ∑ i, j i = h + e)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    (∑ S ∈ (Finset.univ : Finset (Finset (BlockShape p h))).filter
      (fun S => 3 ≤ S.card ∧ shapeSetJoin p S = j ∧ (activeBlocks p S).card = 1),
        shapeCoefficient p theta S ^ 2) ≤
      (1 / 4 : ℝ) ^ 2 * theta ^ 6 * ((e : ℝ) + 1) ^ (3 * k) := by
  let s := (Finset.univ : Finset (Finset (BlockShape p h))).filter
    (fun S => 3 ≤ S.card ∧ shapeSetJoin p S = j ∧ (activeBlocks p S).card = 1)
  by_cases hs : s.Nonempty
  · obtain ⟨S0, hS0⟩ := hs
    obtain ⟨hS03, hS0j, hS01⟩ := (Finset.mem_filter.mp hS0).2
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hS01
    have haJ : a.val.val = j p := by
      rw [← hS0j]
      exact (shapeSetJoin_single_active_coordinate p S0
        (Finset.card_pos.mp (by omega)) a ha).symm
    have hbound := one_block_shape_sum_bound p htheta a (allowedShapeSet p j) s (by
      intro S hS
      obtain ⟨hS3, hSj, hS1⟩ := (Finset.mem_filter.mp hS).2
      obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hS1
      have hbJ : b.val.val = j p := by
        rw [← hSj]
        exact (shapeSetJoin_single_active_coordinate p S
          (Finset.card_pos.mp (by omega)) b hb).symm
      have hba : b = a := Subtype.ext (Fin.ext (hbJ.trans haJ.symm))
      refine ⟨?_, hba ▸ hb, hS3⟩
      rw [← hSj]
      exact shapeSet_subset_allowed_join p S)
    have hc : ((FiniteBlocks.fiber (allowedShapeSet (h := h) p j) a).card : ℝ) ≤ ((e : ℝ) + 1) ^ k := by
      exact_mod_cast card_allowedShapeSet_fiber_le k h e p j hj a haJ
    exact hbound.trans (by
      calc
        _ ≤ (1 / 4 : ℝ) ^ 2 * theta ^ 6 * (((e : ℝ) + 1) ^ k) ^ 3 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 3) (by positivity)
        _ = _ := by rw [← pow_mul, Nat.mul_comm k 3])
  · have hem : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (∑ S ∈ s, shapeCoefficient p theta S ^ 2) ≤ _
    rw [hem, Finset.sum_empty]
    positivity

theorem classII_same_join_activity_bound (k h e : ℕ) (p : Fin (k + 1))
    (j : Fin (k + 1) → ℕ) (hj : ∑ i, j i = h + e)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    (∑ S ∈ (Finset.univ : Finset (Finset (BlockShape p h))).filter
      (fun S => 3 ≤ S.card ∧ shapeSetJoin p S = j ∧ 3 ≤ (activeBlocks p S).card),
        shapeCoefficient p theta S ^ 2) ≤
      (((1 / 4 : ℝ) ^ 2 * theta ^ 2) ^ 3 * ((e : ℝ) + 1) ^ (3 * k) / 6) *
        Real.exp ((1 / 4 : ℝ) ^ 2 * theta ^ 2 * ((e : ℝ) + 1) ^ k) := by
  have hact := shape_classII_join_activity_bound k h e p j hj htheta
  rw [← Finset.sum_filter] at hact
  simp only [Nat.cast_add, Nat.cast_one] at hact
  apply le_trans _ hact
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro S hS
    obtain ⟨_, hjS, hblocks⟩ := (Finset.mem_filter.mp hS).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, hblocks⟩
    rw [← hjS]
    exact shapeSet_subset_allowed_join p S
  · intro S _ _
    positivity

theorem shapeCoefficient_sq_class_split (p : Fin d) (theta : ℝ)
    (S : Finset (BlockShape p h)) :
    shapeCoefficient p theta S ^ 2 ≤
      (if (activeBlocks p S).card = 1 then shapeCoefficient p theta S ^ 2 else 0) +
      (if 3 ≤ (activeBlocks p S).card then shapeCoefficient p theta S ^ 2 else 0) := by
  by_cases h1 : (activeBlocks p S).card = 1
  · rw [if_pos h1]
    exact le_add_of_nonneg_right (by split_ifs <;> positivity)
  · rw [if_neg h1, zero_add]
    by_cases h3 : 3 ≤ (activeBlocks p S).card
    · rw [if_pos h3]
    · rw [if_neg h3]
      have hodd : ¬Odd (activeBlocks p S).card := by
        intro ho
        have hm := Nat.odd_iff.mp ho
        omega
      rw [shapeCoefficient_formula, if_neg hodd]
      norm_num

def joinCoefficientActivity {h : ℕ} (p : Fin d) (theta : ℝ) (j : Fin d → ℕ) : ℝ :=
  ∑ S : Finset (BlockShape p h),
    if 3 ≤ S.card ∧ shapeSetJoin p S = j then shapeCoefficient p theta S ^ 2 else 0

theorem joinCoefficientActivity_class_split (p : Fin d) (theta : ℝ) (j : Fin d → ℕ) :
    joinCoefficientActivity (h := h) p theta j ≤
      (∑ S ∈ (Finset.univ : Finset (Finset (BlockShape p h))).filter
        (fun S => 3 ≤ S.card ∧ shapeSetJoin p S = j ∧ (activeBlocks p S).card = 1),
          shapeCoefficient p theta S ^ 2) +
      (∑ S ∈ (Finset.univ : Finset (Finset (BlockShape p h))).filter
        (fun S => 3 ≤ S.card ∧ shapeSetJoin p S = j ∧ 3 ≤ (activeBlocks p S).card),
          shapeCoefficient p theta S ^ 2) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  by_cases hb : 3 ≤ S.card ∧ shapeSetJoin p S = j
  · have hsplit := shapeCoefficient_sq_class_split p theta S
    simpa only [hb.1, hb.2, true_and, if_true] using hsplit
  · have hf1 : ¬(3 ≤ S.card ∧ shapeSetJoin p S = j ∧ (activeBlocks p S).card = 1) := by tauto
    have hf3 : ¬(3 ≤ S.card ∧ shapeSetJoin p S = j ∧ 3 ≤ (activeBlocks p S).card) := by tauto
    simp only [if_neg hb, if_neg hf1, if_neg hf3, add_zero, le_refl]

theorem joinCoefficientActivity_bound (d h e : ℕ) (hd : 2 ≤ d) (p : Fin d)
    (j : Fin d → ℕ) (hj : ∑ i, j i = h + e) {theta : ℝ} (htheta : 0 ≤ theta) :
    joinCoefficientActivity (h := h) p theta j ≤
      (1 / 4 : ℝ) ^ 2 * theta ^ 6 * ((e : ℝ) + 1) ^ (3 * (d - 2)) +
      (((1 / 4 : ℝ) ^ 2 * theta ^ 2) ^ 3 * ((e : ℝ) + 1) ^ (3 * (d - 1)) / 6) *
        Real.exp ((1 / 4 : ℝ) ^ 2 * theta ^ 2 * ((e : ℝ) + 1) ^ (d - 1)) := by
  cases d with
  | zero => omega
  | succ n =>
    cases n with
    | zero => omega
    | succ k =>
      apply le_trans (joinCoefficientActivity_class_split p theta j)
      exact add_le_add (classI_same_join_activity_bound k h e p j hj htheta)
        (classII_same_join_activity_bound (k + 1) h e p j hj htheta)

abbrev ActualJoinIndex (d h : ℕ) :=
  (e : Fin ((d - 1) * h + 1)) × JoinVectors d (h + e.val)

def actualJoinDepth (J : ActualJoinIndex d h) (i : Fin d) : ℕ := (J.2.val i).val

theorem actualJoinDepth_sum (J : ActualJoinIndex d h) :
    (∑ i, actualJoinDepth J i) = h + J.1.val := J.2.property.1

theorem actualJoinDepth_injective (d h : ℕ) : Function.Injective (@actualJoinDepth d h) := by
  rintro ⟨e,j⟩ ⟨f,k⟩ heq
  have hs := congrArg (fun j : Fin d → ℕ => ∑ i, j i) heq
  have he : e = f := by
    apply Fin.ext
    change (∑ i, (j.val i).val) = ∑ i, (k.val i).val at hs
    rw [j.property.1, k.property.1] at hs
    omega
  subst f
  congr 1
  apply Subtype.ext
  funext i
  exact Fin.ext (congrFun heq i)

def actualJoinIndex (p : Fin d) (S : Finset (BlockShape p h)) (hS : S.Nonempty) :
    ActualJoinIndex d h :=
  ⟨⟨shapeSetExcess p S, Nat.lt_succ_of_le (shapeSetExcess_le p S hS)⟩,
    ⟨fun i => ⟨shapeSetJoin p S i, Nat.lt_succ_of_le (by
      have hc := Dyadic.join_le_shell (S.image (blockShapeEquiv p)) i
      change shapeSetJoin p S i ≤ h at hc
      omega)⟩, shapeSetJoin_sum p S hS, fun i => Dyadic.three_dvd_join _ i⟩⟩

theorem actualJoinIndex_depth (p : Fin d) (S : Finset (BlockShape p h)) (hS : S.Nonempty) :
    actualJoinDepth (actualJoinIndex p S hS) = shapeSetJoin p S := rfl

/-- Exact finite regrouping of the actual shape sets by their actual
join and excess. This is an equality, so no multiplicity is suppressed. -/
theorem shape_sum_group_by_join (p : Fin d) (theta : ℝ) (w : ℕ → ℝ) :
    (∑ S : Finset (BlockShape p h), if 3 ≤ S.card then
      w (shapeSetExcess p S) * shapeCoefficient p theta S ^ 2 else 0) =
      ∑ J : ActualJoinIndex d h,
        w J.1.val * joinCoefficientActivity (h := h) p theta (actualJoinDepth J) := by
  unfold joinCoefficientActivity
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  by_cases h3 : 3 ≤ S.card
  · have hS : S.Nonempty := Finset.card_pos.mp (by omega)
    let J0 := actualJoinIndex p S hS
    have hmatch (J : ActualJoinIndex d h) : shapeSetJoin p S = actualJoinDepth J ↔ J = J0 := by
      constructor
      · intro hJ
        apply actualJoinDepth_injective d h
        exact hJ.symm
      · rintro rfl
        rfl
    simp only [h3, true_and, if_true]
    simp_rw [hmatch]
    rw [Finset.sum_eq_single J0]
    · simp only [J0, actualJoinIndex, if_true]
    · intro J _ hJ
      simp only [if_neg hJ, mul_zero]
    · simp
  · simp only [h3, false_and, if_false, mul_zero, Finset.sum_const_zero]

end Tusnady.Witness
