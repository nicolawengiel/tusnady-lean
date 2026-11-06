import Mathlib.Analysis.Convex.Join
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# A closed convex lift of two compact sets

The sets A and B are placed at heights zero and one. The convex join has
exactly their weighted Minkowski mixtures as horizontal sections. Compactness
comes from an explicit continuous image of A × B × [0,1].
-/
noncomputable section
open Set
open scoped Pointwise
namespace OAI.GaussianPropeller.ConvexLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The lifted convex join; this definition makes no convexity assumption. -/
def lift (A B : Set E) : Set (E × ℝ) :=
  convexJoin ℝ (A ×ˢ ({0} : Set ℝ)) (B ×ˢ ({1} : Set ℝ))

/-- An indexed description of the actual weighted Minkowski mixture. -/
def mixture (A B : Set E) (a c : ℝ) : Set E :=
  {z | ∃ x ∈ A, ∃ y ∈ B, a • x + c • y = z}

/-- This is the ordinary pointwise Minkowski sum notation. -/
theorem mixture_eq_smul_add (A B : Set E) (a c : ℝ) :
    mixture A B a c = a • A + c • B := by
  ext z
  simp only [mixture, mem_setOf_eq, Set.mem_add, Set.mem_smul_set]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨a • x, ⟨x, hx, rfl⟩, c • y, ⟨y, hy, rfl⟩, hxy⟩
  · rintro ⟨u, ⟨x, hx, hxu⟩, w, ⟨y, hy, hyw⟩, huw⟩
    exact ⟨x, hx, y, hy, by simpa only [hxu, hyw] using huw⟩

/-- Exact membership, including both endpoint heights. -/
theorem mem_lift_iff (A B : Set E) (z : E) (t : ℝ) :
    (z, t) ∈ lift A B ↔ ∃ x ∈ A, ∃ y ∈ B, ∃ a c : ℝ,
      0 ≤ a ∧ 0 ≤ c ∧ a + c = 1 ∧ a • x + c • y = z ∧ c = t := by
  constructor
  · intro h
    obtain ⟨⟨x, r⟩, ⟨hx, hr⟩, ⟨y, s⟩, ⟨hy, hs⟩, a, c, ha, hc, hac, heq⟩ :=
      mem_convexJoin.mp h
    simp only [mem_singleton_iff] at hr hs
    subst r
    subst s
    have hfst := congrArg Prod.fst heq
    have hsnd := congrArg Prod.snd heq
    change a • x + c • y = z at hfst
    change a * 0 + c * 1 = t at hsnd
    simp only [mul_zero, mul_one, zero_add] at hsnd
    exact ⟨x, hx, y, hy, a, c, ha, hc, hac, hfst, hsnd⟩
  · rintro ⟨x, hx, y, hy, a, c, ha, hc, hac, hxy, hct⟩
    apply mem_convexJoin.mpr
    refine ⟨(x, 0), ⟨hx, by simp⟩, (y, 1), ⟨hy, by simp⟩, a, c, ha, hc, hac, ?_⟩
    apply Prod.ext
    · exact hxy
    · simpa using hct

/-- Every height in the lift lies in the closed unit interval. -/
theorem height_mem_Icc {A B : Set E} {z : E} {t : ℝ} (h : (z, t) ∈ lift A B) :
    t ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨x, hx, y, hy, a, c, ha, hc, hac, hxy, rfl⟩ := (mem_lift_iff A B z t).mp h
  exact ⟨hc, by linarith⟩

/-- Horizontal sections are exactly the stated weighted Minkowski mixtures. -/
theorem mem_lift_at_weights (A B : Set E) (z : E) {a c : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) :
    (z, c) ∈ lift A B ↔ z ∈ mixture A B a c := by
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, a', c', ha', hc', hac', hxy, hcc⟩ := (mem_lift_iff A B z c).mp h
    have haa : a' = a := by linarith
    exact ⟨x, hx, y, hy, by simpa only [haa, hcc] using hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact (mem_lift_iff A B z c).mpr ⟨x, hx, y, hy, a, c, ha, hc, hac, hxy, rfl⟩

theorem section_lift (A B : Set E) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    {z : E | (z, t) ∈ lift A B} = mixture A B (1 - t) t := by
  ext z
  exact mem_lift_at_weights A B z (by linarith [ht.2]) ht.1 (by ring)

theorem section_zero (A B : Set E) (hB : B.Nonempty) :
    {z : E | (z, (0 : ℝ)) ∈ lift A B} = A := by
  ext z
  rw [mem_setOf_eq, mem_lift_at_weights A B z (a := 1) (by norm_num) (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨x, hx, y, hy, heq⟩
    simp only [one_smul, zero_smul, add_zero] at heq
    exact heq ▸ hx
  · intro hz
    obtain ⟨y, hy⟩ := hB
    exact ⟨z, hz, y, hy, by simp⟩

theorem section_one (A B : Set E) (hA : A.Nonempty) :
    {z : E | (z, (1 : ℝ)) ∈ lift A B} = B := by
  ext z
  rw [mem_setOf_eq, mem_lift_at_weights A B z (a := 0) (by norm_num) (by norm_num) (by norm_num)]
  constructor
  · rintro ⟨x, hx, y, hy, heq⟩
    simp only [one_smul, zero_smul, zero_add] at heq
    exact heq ▸ hy
  · intro hz
    obtain ⟨x, hx⟩ := hA
    exact ⟨x, hx, z, hz, by simp⟩

/-- Convexity is inherited from the endpoint sets. -/
theorem convex_lift {A B : Set E} (hA : Convex ℝ A) (hB : Convex ℝ B) :
    Convex ℝ (lift A B) :=
  (hA.prod (convex_singleton (0 : ℝ))).convexJoin (hB.prod (convex_singleton (1 : ℝ)))

/-- An explicit compact parametrization, with no choice of minimizers. -/
theorem lift_eq_image (A B : Set E) :
    lift A B = (fun p : (E × E) × ℝ => ((1 - p.2) • p.1.1 + p.2 • p.1.2, p.2)) ''
      ((A ×ˢ B) ×ˢ Icc (0 : ℝ) 1) := by
  ext p
  rcases p with ⟨z, t⟩
  constructor
  · intro hp
    obtain ⟨x, hx, y, hy, a, c, ha, hc, hac, hxy, hct⟩ := (mem_lift_iff A B z t).mp hp
    have ha' : a = 1 - c := by linarith
    refine ⟨((x, y), c), ⟨⟨hx, hy⟩, hc, by linarith⟩, ?_⟩
    apply Prod.ext
    · simpa only [← ha'] using hxy
    · exact hct
  · rintro ⟨⟨⟨x, y⟩, c⟩, ⟨⟨hx, hy⟩, hc, hc1⟩, hp⟩
    apply (mem_lift_iff A B z t).mpr
    refine ⟨x, hx, y, hy, 1 - c, c, by linarith, hc, by ring, ?_, ?_⟩
    · exact congrArg Prod.fst hp
    · exact congrArg Prod.snd hp

theorem isCompact_lift {A B : Set E} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact (lift A B) := by
  rw [lift_eq_image]
  apply ((hA.prod hB).prod isCompact_Icc).image
  fun_prop

theorem isClosed_lift {A B : Set E} (hA : IsCompact A) (hB : IsCompact B) :
    IsClosed (lift A B) := (isCompact_lift hA hB).isClosed

end OAI.GaussianPropeller.ConvexLift
