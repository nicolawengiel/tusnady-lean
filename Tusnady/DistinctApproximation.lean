import Mathlib.Topology.Constructions
import Mathlib.Topology.Perfect
import Mathlib.Data.Fin.Tuple.Basic

/-! Finite tuples with distinct entries occur in every product neighborhood
when the underlying space has no finite neighborhoods. -/

noncomputable section
open Set Filter
open scoped Topology
namespace Tusnady.DistinctApproximation

lemma exists_injective_mem {X : Type*} (m : ℕ) (s : Fin m → Set X)
    (hs : ∀ i, (s i).Infinite) :
    ∃ P : Fin m → X, Function.Injective P ∧ ∀ i, P i ∈ s i := by
  classical
  induction m with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    obtain ⟨Q, hQ, hQs⟩ := ih (fun i => s i.succ) (fun i => hs i.succ)
    obtain ⟨x, hx, hxQ⟩ := (hs 0).exists_notMem_finite (Set.finite_range Q)
    refine ⟨Fin.cons x Q, Fin.cons_injective_of_injective hxQ hQ, ?_⟩
    intro i
    exact Fin.cases hx (fun j => hQs j) i

lemma exists_injective_in_nhds {X : Type*} [TopologicalSpace X]
    (hinf : ∀ (x : X) (s : Set X), s ∈ 𝓝 x → s.Infinite)
    {m : ℕ} (P : Fin m → X) (U : Set (Fin m → X)) (hU : U ∈ 𝓝 P) :
    ∃ Q ∈ U, Function.Injective Q := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, _, s, hs, hsU⟩ := hU
  obtain ⟨Q, hQ, hQs⟩ := exists_injective_mem m s (fun i => hinf (P i) (s i) (hs i))
  exact ⟨Q, hsU (fun i _ => hQs i), hQ⟩

end Tusnady.DistinctApproximation
