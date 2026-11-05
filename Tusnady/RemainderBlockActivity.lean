import Tusnady.RemainderActivity

/-! # Actual finite factorization of block activities

Every subset of the disjoint union is accounted for exactly once by its
nonempty block fibers. The factorization is proved, not an independence
or activity hypothesis.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.RemainderActivity
attribute [local instance] Classical.propDecidable
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {B : A → Type*} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

def active (T : Finset (Σ a, B a)) : Finset A :=
  Finset.univ.filter (fun a => FiniteBlocks.fiber T a ≠ ∅)

def blockActivity (w : (a : A) → Finset (B a) → ℝ) (a : A) : ℝ :=
  ∑ t : Finset (B a), if t = ∅ then 0 else w a t

def productWeight (w : (a : A) → Finset (B a) → ℝ) (T : Finset (Σ a, B a)) : ℝ :=
  ∏ a : A, if FiniteBlocks.fiber T a = ∅ then 1 else w a (FiniteBlocks.fiber T a)

private def maskedBlockWeight (w : (a : A) → Finset (B a) → ℝ)
    (S : Finset A) (a : A) (t : Finset (B a)) : ℝ :=
  if a ∈ S then (if t = ∅ then 0 else w a t) else (if t = ∅ then 1 else 0)

private theorem maskedBlockWeight_prod (w : (a : A) → Finset (B a) → ℝ)
    (S : Finset A) (T : Finset (Σ a, B a)) :
    (∏ a : A, maskedBlockWeight w S a (FiniteBlocks.fiber T a)) =
      if active T = S then productWeight w T else 0 := by
  by_cases heq : active T = S
  · rw [if_pos heq]
    apply Finset.prod_congr rfl
    intro a _
    have ham : a ∈ S ↔ FiniteBlocks.fiber T a ≠ ∅ := by
      rw [← heq]
      simp [active]
    by_cases ht : FiniteBlocks.fiber T a = ∅
    · have ha : a ∉ S := fun h => ham.mp h ht
      simp [maskedBlockWeight, ha, ht]
    · have ha : a ∈ S := ham.mpr ht
      simp [maskedBlockWeight, ha, ht]
  · rw [if_neg heq]
    obtain ⟨a, ha⟩ : ∃ a, ¬(a ∈ active T ↔ a ∈ S) := by
      simpa only [Finset.ext_iff, not_forall] using heq
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    by_cases ht : FiniteBlocks.fiber T a = ∅ <;> by_cases hm : a ∈ S
    · simp [maskedBlockWeight, ht, hm]
    · exact (ha (by simp [active, ht, hm])).elim
    · exact (ha (by simp [active, ht, hm])).elim
    · simp [maskedBlockWeight, ht, hm]

theorem fixed_active_factorization (w : (a : A) → Finset (B a) → ℝ) (S : Finset A) :
    (∑ T : Finset (Σ a, B a), if active T = S then productWeight w T else 0) =
      ∏ a ∈ S, blockActivity w a := by
  have h := FiniteBlocks.product_expansion (maskedBlockWeight w S)
    (fun _ : Σ a, B a => (1 : ℝ))
  simp only [Finset.prod_const_one, mul_one, maskedBlockWeight_prod] at h
  have hsum (a : A) : (∑ t : Finset (B a), maskedBlockWeight w S a t) =
      if a ∈ S then blockActivity w a else 1 := by
    by_cases ha : a ∈ S
    · simp only [maskedBlockWeight, if_pos ha, blockActivity]
    · simp [maskedBlockWeight, ha]
  simp_rw [hsum] at h
  simpa only [Finset.prod_ite_mem, Finset.univ_inter] using h.symm

theorem active_tail_factorization (w : (a : A) → Finset (B a) → ℝ) (k : ℕ) :
    (∑ T : Finset (Σ a, B a), if k ≤ (active T).card then productWeight w T else 0) =
      tail (blockActivity w) Finset.univ k := by
  have hsingle (T : Finset (Σ a, B a)) :
      (if k ≤ (active T).card then productWeight w T else 0) =
        ∑ S : Finset A, if k ≤ S.card then
          (if active T = S then productWeight w T else 0) else 0 := by
    rw [Finset.sum_eq_single (active T)]
    · simp
    · intro S _ hS
      simp [Ne.symm hS]
    · simp
  simp_rw [hsingle]
  rw [Finset.sum_comm]
  unfold tail
  simp only [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hk : k ≤ S.card
  · simp only [if_pos hk]
    exact fixed_active_factorization w S
  · simp [hk]

theorem active_tail_three_bound (w : (a : A) → Finset (B a) → ℝ)
    (hw : ∀ a t, 0 ≤ w a t) :
    (∑ T : Finset (Σ a, B a), if 3 ≤ (active T).card then productWeight w T else 0) ≤
      (∑ a : A, blockActivity w a) ^ 3 / 6 * Real.exp (∑ a : A, blockActivity w a) := by
  rw [active_tail_factorization]
  apply tail_three_le
  intro a _
  apply Finset.sum_nonneg
  intro t _
  split_ifs
  · rfl
  · exact hw a t

def restrictedWeight (w : (a : A) → Finset (B a) → ℝ)
    (E : Finset (Σ a, B a)) (a : A) (t : Finset (B a)) : ℝ :=
  if t ⊆ FiniteBlocks.fiber E a then w a t else 0

omit [Fintype A] in
theorem fiber_subset_iff (T E : Finset (Σ a, B a)) :
    T ⊆ E ↔ ∀ a, FiniteBlocks.fiber T a ⊆ FiniteBlocks.fiber E a := by
  constructor
  · intro h a b hb
    have hmem : (⟨a,b⟩ : Σ a, B a) ∈ T := by simpa [FiniteBlocks.fiber] using hb
    simpa [FiniteBlocks.fiber] using h hmem
  · intro h x hx
    rcases x with ⟨a,b⟩
    have hb : b ∈ FiniteBlocks.fiber T a := by simpa [FiniteBlocks.fiber] using hx
    simpa [FiniteBlocks.fiber] using h a hb

theorem restricted_productWeight (w : (a : A) → Finset (B a) → ℝ)
    (E T : Finset (Σ a, B a)) :
    productWeight (restrictedWeight w E) T = if T ⊆ E then productWeight w T else 0 := by
  by_cases hTE : T ⊆ E
  · rw [if_pos hTE]
    apply Finset.prod_congr rfl
    intro a _
    simp only [restrictedWeight, if_pos ((fiber_subset_iff T E).mp hTE a)]
  · rw [if_neg hTE]
    have hf : ∃ a, ¬FiniteBlocks.fiber T a ⊆ FiniteBlocks.fiber E a := by
      simpa only [fiber_subset_iff, not_forall] using hTE
    obtain ⟨a, ha⟩ := hf
    have hne : FiniteBlocks.fiber T a ≠ ∅ := by
      intro he
      exact ha (he ▸ Finset.empty_subset _)
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [hne, restrictedWeight, ha]

theorem restricted_active_tail_three_bound (w : (a : A) → Finset (B a) → ℝ)
    (hw : ∀ a t, 0 ≤ w a t) (E : Finset (Σ a, B a)) :
    (∑ T : Finset (Σ a, B a), if T ⊆ E ∧ 3 ≤ (active T).card then productWeight w T else 0) ≤
      (∑ a : A, blockActivity (restrictedWeight w E) a) ^ 3 / 6 *
        Real.exp (∑ a : A, blockActivity (restrictedWeight w E) a) := by
  have h := active_tail_three_bound (restrictedWeight w E) (by
    intro a t
    unfold restrictedWeight
    split_ifs
    · exact hw a t
    · rfl)
  simp_rw [restricted_productWeight] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro T _
  by_cases he : T ⊆ E <;> by_cases hk : 3 ≤ (active T).card <;> simp [he, hk]

theorem productWeight_eq_prod_active (w : (a : A) → Finset (B a) → ℝ)
    (T : Finset (Σ a, B a)) :
    productWeight w T = ∏ a ∈ active T, w a (FiniteBlocks.fiber T a) := by
  unfold productWeight
  symm
  calc
    (∏ a ∈ active T, w a (FiniteBlocks.fiber T a)) =
        ∏ a ∈ active T, if FiniteBlocks.fiber T a = ∅ then 1 else w a (FiniteBlocks.fiber T a) := by
      apply Finset.prod_congr rfl
      intro a ha
      have hne : FiniteBlocks.fiber T a ≠ ∅ := (Finset.mem_filter.mp ha).2
      rw [if_neg hne]
    _ = _ := Finset.prod_subset (Finset.subset_univ _) (by
      intro a _ ha
      have hem : FiniteBlocks.fiber T a = ∅ := by simpa [active] using ha
      simp [hem])

theorem sum_card_fiber (E : Finset (Σ a, B a)) :
    (∑ a : A, (FiniteBlocks.fiber E a).card) = E.card := by
  have h := congrArg Finset.card (FiniteBlocks.assemble_fiber E)
  simpa only [FiniteBlocks.assemble, Finset.card_sigma] using h

end Tusnady.RemainderActivity
