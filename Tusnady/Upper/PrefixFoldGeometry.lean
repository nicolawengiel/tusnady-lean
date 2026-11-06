import Tusnady.Upper.PrefixBalancing
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic.Module

/-!
# Geometry of the actual Banaszczyk fold

For a convex set `K`, the fold is the sum of the two-translate intersection
`{c | c-u ∈ K ∧ c+u ∈ K}` and the segment `[-2u,2u]`.  On each line parallel
to `u`, this is exactly Banaszczyk's transform: delete sections shorter than
`2 ‖u‖` and expand the remaining sections by `u` in both directions.

All geometric rules needed by `PrefixBalancing` are proved here.  The Gaussian
measure monotonicity of this concrete fold is not asserted by this file.
-/

noncomputable section
open Set

namespace Tusnady.Upper

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def foldCore (K : Set E) (u : E) : Set E := {c | c - u ∈ K ∧ c + u ∈ K}

/-- Algebraic form of Banaszczyk's closed fold. -/
def signingFold (u : E) (K : Set E) : Set E :=
  (fun p : E × ℝ => p.1 + p.2 • u) '' (foldCore K u ×ˢ Set.Icc (-2 : ℝ) 2)

theorem mem_signingFold_iff (K : Set E) (u x : E) :
    x ∈ signingFold u K ↔ ∃ c : E, ∃ t : ℝ,
      c - u ∈ K ∧ c + u ∈ K ∧ t ∈ Set.Icc (-2 : ℝ) 2 ∧ x = c + t • u := by
  constructor
  · rintro ⟨⟨c, t⟩, ⟨hc, ht⟩, h⟩
    exact ⟨c, t, hc.1, hc.2, ht, h.symm⟩
  · rintro ⟨c, t, hm, hp, ht, rfl⟩
    exact ⟨(c, t), ⟨⟨hm, hp⟩, ht⟩, rfl⟩

@[simp] theorem signingFold_zero (K : Set E) : signingFold (0 : E) K = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨c, t, hc, _, _, rfl⟩ := (mem_signingFold_iff K 0 x).1 hx
    simpa using hc
  · intro hx
    exact (mem_signingFold_iff K 0 x).2
      ⟨x, 0, by simpa using hx, by simpa using hx, by norm_num, by simp⟩

theorem convex_foldCore (K : Set E) (hK : Convex ℝ K) (u : E) :
    Convex ℝ (foldCore K u) := by
  change Convex ℝ ((fun x => x - u) ⁻¹' K ∩ (fun x => x + u) ⁻¹' K)
  simpa only [sub_eq_add_neg] using
    (hK.translate_preimage_left (-u)).inter (hK.translate_preimage_left u)

theorem convex_signingFold (K : Set E) (hK : Convex ℝ K) (u : E) :
    Convex ℝ (signingFold u K) := by
  let f : E × ℝ →ₗ[ℝ] E :=
    { toFun := fun p => p.1 + p.2 • u
      map_add' := by intro p q; dsimp; module
      map_smul' := by intro r p; dsimp; module }
  exact ((convex_foldCore K hK u).prod (convex_Icc (-2 : ℝ) 2)).linear_image f

theorem mem_centered_segment (K : Set E) (hK : Convex ℝ K) (c u : E)
    (hm : c - u ∈ K) (hp : c + u ∈ K) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    c + t • u ∈ K := by
  have h := hK hm hp (a := (1 - t) / 2) (b := (1 + t) / 2)
    (by linarith [ht.2]) (by linarith [ht.1]) (by ring)
  convert h using 1; module

/-- Every point of the fold has at least one signed predecessor in `K`. -/
theorem signingFold_step (K : Set E) (hK : Convex ℝ K) (u x : E)
    (hx : x ∈ signingFold u K) : x + u ∈ K ∨ x - u ∈ K := by
  obtain ⟨⟨c, t⟩, ⟨hc, ht⟩, rfl⟩ := hx
  by_cases htn : t ≤ 0
  · left
    have h := mem_centered_segment K hK c u hc.1 hc.2 (t + 1)
      ⟨by linarith [ht.1], by linarith⟩
    convert h using 1; module
  · right
    have h := mem_centered_segment K hK c u hc.1 hc.2 (t - 1)
      ⟨by linarith, by linarith [ht.2]⟩
    convert h using 1; module

/-- The fold preserves origin symmetry. -/
theorem symmetric_signingFold (K : Set E) (hK : ∀ x ∈ K, -x ∈ K) (u : E) :
    ∀ x ∈ signingFold u K, -x ∈ signingFold u K := by
  rintro x ⟨⟨c, t⟩, ⟨hc, ht⟩, rfl⟩
  refine ⟨(-c, -t), ⟨?_, ?_⟩, ?_⟩
  · constructor
    · convert hK (c + u) hc.2 using 1; module
    · convert hK (c - u) hc.1 using 1; module
  · exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  · dsimp
    module

section Topology

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [ContinuousSMul ℝ E]

omit [Module ℝ E] [T2Space E] [ContinuousSMul ℝ E] in
theorem isClosed_foldCore (K : Set E) (hK : IsClosed K) (u : E) :
    IsClosed (foldCore K u) :=
  (hK.preimage (continuous_id.sub continuous_const)).inter
    (hK.preimage (continuous_id.add continuous_const))

omit [Module ℝ E] [ContinuousSMul ℝ E] in
theorem isCompact_foldCore (K : Set E) (hK : IsCompact K) (u : E) :
    IsCompact (foldCore K u) := by
  apply (hK.image (show Continuous (fun z : E => z + u) from
    continuous_id.add continuous_const)).of_isClosed_subset
    (isClosed_foldCore K hK.isClosed u)
  intro c hc
  exact ⟨c - u, hc.1, by simp⟩

theorem isCompact_signingFold (K : Set E) (hK : IsCompact K) (u : E) :
    IsCompact (signingFold u K) :=
  ((isCompact_foldCore K hK u).prod isCompact_Icc).image
    (continuous_fst.add (continuous_snd.smul continuous_const))

theorem isClosed_signingFold (K : Set E) (hK : IsCompact K) (u : E) :
    IsClosed (signingFold u K) := (isCompact_signingFold K hK u).isClosed

end Topology

section Measure

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
    [ContinuousSMul ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The concrete geometric rules are now discharged.  Only the explicitly
displayed Gaussian measure-monotonicity theorem remains an analytic input.
`A ⊆ K` and closedness make every such `A` compact, so no full-dimensional or
nonempty-interior hypothesis is being hidden in the recursive bodies. -/
theorem signingFold_transformRules (μ : MeasureTheory.Measure E) (K : Set E)
    (hKcomp : IsCompact K) (hKconv : Convex ℝ K) (hKsymm : ∀ x ∈ K, -x ∈ K)
    (Allowed : E → Prop)
    (hmass : ∀ A : Set E, IsCompact A → Convex ℝ A → (∀ x ∈ A, -x ∈ A) →
      ∀ u : E, Allowed u → (1 : ℝ) / 2 ≤ μ.real A →
        μ.real A ≤ μ.real (signingFold u A)) :
    TransformRules μ K
      (fun A => IsClosed A ∧ Convex ℝ A ∧ ∀ x ∈ A, -x ∈ A)
      Allowed signingFold := by
  refine
    { good_univ := ⟨isClosed_univ, convex_univ, fun _ _ => Set.mem_univ _⟩
      good_K := ⟨hKcomp.isClosed, hKconv, hKsymm⟩
      good_inter := ?_
      measurable := fun _ hA => hA.1.measurableSet
      good_transform := ?_
      mass_mono := ?_
      step := ?_
      zero_mem := ?_ }
  · intro A B hA hB
    exact ⟨hA.1.inter hB.1, hA.2.1.inter hB.2.1,
      fun x hx => ⟨hA.2.2 x hx.1, hB.2.2 x hx.2⟩⟩
  · intro u A _ hA hAK
    have hcomp : IsCompact A := hKcomp.of_isClosed_subset hA.1 hAK
    exact ⟨isClosed_signingFold A hcomp u, convex_signingFold A hA.2.1 u,
      symmetric_signingFold A hA.2.2 u⟩
  · intro u A hu hA hAK hhalf
    exact hmass A (hKcomp.of_isClosed_subset hA.1 hAK) hA.2.1 hA.2.2 u hu hhalf
  · intro u A hA x hx
    exact signingFold_step A hA.2.1 u x hx
  · intro A hA hhalf
    exact zero_mem_of_convex_symmetric_mass μ A hA.2.1 hA.2.2 (by linarith)

end Measure
end Tusnady.Upper
