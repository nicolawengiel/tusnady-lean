import Tusnady.Definitions
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# The finite prefix step in Banaszczyk's signed-series argument

This file proves the combinatorial and probability bookkeeping which turns a
Gaussian-measure-monotone signing transform into ONE choice of signs valid for
EVERY prefix.  It does not assert that the analytic transform exists.  In
particular, `TransformRules` below is an explicit parameter of the reduction,
not a proved version of Banaszczyk's theorem and not a project axiom.

The analytic input still to be proved is Banaszczyk's transform monotonicity
(1998, Theorem 3), used for the signed-series theorem (2012) and Nikolov (2017),
Lemma 9.  Szusterman, arXiv:2510.00842, Theorem 1.3, supplies an alternative
analytic proof with universal factor 7 instead of 5.
-/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Tusnady.Upper

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- One fixed sign function is used in all the finite sums. -/
def prefixSum (v : ℕ → E) (χ : ℕ → Bool) (k : ℕ) : E :=
  ∑ i ∈ Finset.range k, Tusnady.sign (χ i) • v i

/-- Reverse recursion: reaching the next kernel is required to put the next
partial sum back into `K`.  The empty tail places no further restriction. -/
def prefixKernel (T : E → Set E → Set E) (K : Set E) : ℕ → (ℕ → E) → Set E
  | 0, _ => Set.univ
  | n + 1, v => T (v 0) (K ∩ prefixKernel T K n (fun i => v (i + 1)))

/-- The elementary selection part of the signed-series proof.  The analytic
content of the transform is deliberately absent from this theorem. -/
theorem prefix_signs_of_mem_kernel (T : E → Set E → Set E) (K : Set E)
    (Allowed : E → Prop)
    (hstep : ∀ m (w : ℕ → E) x, (∀ i, i < m + 1 → Allowed (w i)) →
      x ∈ prefixKernel T K (m + 1) w →
      x + w 0 ∈ K ∩ prefixKernel T K m (fun i => w (i + 1)) ∨
        x - w 0 ∈ K ∩ prefixKernel T K m (fun i => w (i + 1)))
    (n : ℕ) (v : ℕ → E) (hv : ∀ i, i < n → Allowed (v i))
    (x : E) (hx : x ∈ prefixKernel T K n v) :
    ∃ χ : ℕ → Bool, ∀ k, 0 < k → k ≤ n → x + prefixSum v χ k ∈ K := by
  induction n generalizing v x with
  | zero =>
      exact ⟨fun _ => false, fun k hk hkn => False.elim (by omega)⟩
  | succ n ih =>
      have hx' := hstep n v x hv hx
      have hchoice : ∃ b : Bool,
          x + Tusnady.sign b • v 0 ∈ K ∩ prefixKernel T K n (fun i => v (i + 1)) := by
        rcases hx' with hp | hm
        · exact ⟨true, by simpa [Tusnady.sign] using hp⟩
        · exact ⟨false, by simpa [Tusnady.sign, sub_eq_add_neg] using hm⟩
      obtain ⟨b, hb⟩ := hchoice
      obtain ⟨χ, hχ⟩ := ih (fun i => v (i + 1))
        (fun i hi => hv (i + 1) (by omega)) (x + Tusnady.sign b • v 0) hb.2
      let ψ : ℕ → Bool := fun i => match i with | 0 => b | j + 1 => χ j
      refine ⟨ψ, ?_⟩
      intro k hk hkn
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      have hsum : prefixSum v ψ (j + 1) = Tusnady.sign b • v 0 +
          prefixSum (fun i => v (i + 1)) χ j := by
        simp [prefixSum, Finset.sum_range_succ', ψ, add_comm]
      rw [hsum, ← add_assoc]
      by_cases hj : j = 0
      · subst j
        simpa [prefixSum] using hb.1
      · exact hχ j (Nat.pos_of_ne_zero hj) (by omega)

section Measure

variable [MeasurableSpace E]

omit [AddCommGroup E] [Module ℝ E] in
/-- The union bound in the real-valued probability-measure convention. -/
theorem probability_inter_lower (μ : Measure E) [IsProbabilityMeasure μ]
    (A B : Set E) (hB : MeasurableSet B) :
    μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B) := by
  have h := measureReal_union_add_inter (μ := μ) (s := A) hB
  have hu : μ.real (A ∪ B) ≤ 1 := by
    simpa using measureReal_mono (μ := μ) (Set.subset_univ (A ∪ B))
  linarith

/-- For symmetric convex sets, the origin conclusion only needs positive mass;
no Gaussian separation or dimension hypothesis is required. -/
theorem zero_mem_of_convex_symmetric_mass (μ : Measure E) (A : Set E)
    (hconv : Convex ℝ A) (hsymm : ∀ x ∈ A, -x ∈ A)
    (hmass : 0 < μ.real A) : (0 : E) ∈ A := by
  obtain ⟨x, hx⟩ := nonempty_of_measureReal_ne_zero hmass.ne'
  simpa using hconv.midpoint_mem hx (hsymm x hx)

/-- Exact local rules needed in the prefix reduction.  `Good` may, for example,
mean closed, convex, origin-symmetric.  The transform is only needed on subsets
of the fixed target `K`; this permits a compact-body analytic theorem even
though the zero-length kernel is `univ`.

This structure is an explicit *unproved analytic input*, pending construction
of the actual Gaussian transform.  No inhabitant is postulated in this file. -/
structure TransformRules (μ : Measure E) (K : Set E) (Good : Set E → Prop)
    (Allowed : E → Prop) (T : E → Set E → Set E) : Prop where
  good_univ : Good Set.univ
  good_K : Good K
  good_inter : ∀ A B, Good A → Good B → Good (A ∩ B)
  measurable : ∀ A, Good A → MeasurableSet A
  good_transform : ∀ v A, Allowed v → Good A → A ⊆ K → Good (T v A)
  mass_mono : ∀ v A, Allowed v → Good A → A ⊆ K →
    (1 : ℝ) / 2 ≤ μ.real A → μ.real A ≤ μ.real (T v A)
  step : ∀ v A, Good A → ∀ x, x ∈ T v A → x + v ∈ A ∨ x - v ∈ A
  zero_mem : ∀ A, Good A → (1 : ℝ) / 2 ≤ μ.real A → (0 : E) ∈ A

variable (μ : Measure E) [IsProbabilityMeasure μ] (K : Set E)
    (Good : Set E → Prop) (Allowed : E → Prop) (T : E → Set E → Set E)
    (rules : TransformRules μ K Good Allowed T)

include rules

omit [Module ℝ E] [IsProbabilityMeasure μ] in
/-- The geometric admissibility invariant is independent of the measure
estimate.  Even empty kernels remain admissible. -/
theorem prefixKernel_good (n : ℕ) (v : ℕ → E)
    (hv : ∀ i, i < n → Allowed (v i)) : Good (prefixKernel T K n v) := by
  induction n generalizing v with
  | zero => exact rules.good_univ
  | succ n ih =>
      have ht := ih (fun i => v (i + 1)) (fun i hi => hv (i + 1) (by omega))
      exact rules.good_transform _ _ (hv 0 (by omega))
        (rules.good_inter _ _ rules.good_K ht) Set.inter_subset_left

omit [Module ℝ E] in
/-- Every intermediate kernel is admissible; the Gaussian threshold is checked
at each transform, with an explicit loss of at most `δ` per new prefix. -/
theorem prefixKernel_mass (δ : ℝ) (hδ : 0 ≤ δ) (hK : 1 - δ ≤ μ.real K)
    (n : ℕ) (hn : (n : ℝ) * δ ≤ (1 : ℝ) / 2)
    (v : ℕ → E) (hv : ∀ i, i < n → Allowed (v i)) :
    Good (prefixKernel T K n v) ∧
      1 - (n : ℝ) * δ ≤ μ.real (prefixKernel T K n v) := by
  induction n generalizing v with
  | zero =>
      simpa [prefixKernel] using And.intro rules.good_univ (le_refl (1 : ℝ))
  | succ n ih =>
      have hn' : (n : ℝ) * δ ≤ (1 : ℝ) / 2 := by
        push_cast at hn
        nlinarith
      obtain ⟨hg, hm⟩ := ih hn' (fun i => v (i + 1)) (fun i hi => hv (i + 1) (by omega))
      let A := K ∩ prefixKernel T K n (fun i => v (i + 1))
      have hA : Good A := rules.good_inter _ _ rules.good_K hg
      have hmass : 1 - ((n : ℝ) + 1) * δ ≤ μ.real A := by
        have hi := probability_inter_lower μ K
          (prefixKernel T K n (fun i => v (i + 1))) (rules.measurable _ hg)
        dsimp [A]
        linarith
      have hhalf : (1 : ℝ) / 2 ≤ μ.real A := by
        push_cast at hn
        linarith
      constructor
      · exact rules.good_transform _ A (hv 0 (by omega)) hA Set.inter_subset_left
      · have ht := rules.mass_mono (v 0) A (hv 0 (by omega)) hA Set.inter_subset_left hhalf
        change 1 - ((n + 1 : ℕ) : ℝ) * δ ≤ μ.real (T (v 0) A)
        push_cast
        linarith

/-- The full finite prefix conclusion, conditional precisely on the transform
rules above.  The signs precede the universal quantifier over prefix lengths. -/
theorem prefix_signing_of_transform (δ : ℝ) (hδ : 0 ≤ δ)
    (hK : 1 - δ ≤ μ.real K) (n : ℕ)
    (hn : (n : ℝ) * δ ≤ (1 : ℝ) / 2) (v : ℕ → E)
    (hv : ∀ i, i < n → Allowed (v i)) :
    ∃ χ : ℕ → Bool, ∀ k, 0 < k → k ≤ n → prefixSum v χ k ∈ K := by
  obtain ⟨hg, hm⟩ := prefixKernel_mass μ K Good Allowed T rules δ hδ hK n hn v hv
  have hhalf : (1 : ℝ) / 2 ≤ μ.real (prefixKernel T K n v) := by linarith
  have hz := rules.zero_mem _ hg hhalf
  have hstep : ∀ m (w : ℕ → E) x, (∀ i, i < m + 1 → Allowed (w i)) →
      x ∈ prefixKernel T K (m + 1) w →
      x + w 0 ∈ K ∩ prefixKernel T K m (fun i => w (i + 1)) ∨
        x - w 0 ∈ K ∩ prefixKernel T K m (fun i => w (i + 1)) := by
    intro m w x hw hx
    have hg' := prefixKernel_good μ K Good Allowed T rules m (fun i => w (i + 1))
      (fun i hi => hw (i + 1) (by omega))
    exact rules.step _ _ (rules.good_inter _ _ rules.good_K hg') x hx
  simpa only [zero_add] using prefix_signs_of_mem_kernel T K Allowed hstep n v hv 0 hz

/-- The same conclusion with exactly `n` sign choices.  Prefix `k` is the sum
over the first `k` entries in the prescribed order, including ties in any
application's separately chosen ordering. -/
theorem prefix_signing_fin_of_transform (δ : ℝ) (hδ : 0 ≤ δ)
    (hK : 1 - δ ≤ μ.real K) (n : ℕ)
    (hn : (n : ℝ) * δ ≤ (1 : ℝ) / 2) (v : Fin n → E)
    (hv : ∀ i, Allowed (v i)) :
    ∃ χ : Fin n → Bool, ∀ k (hk : k ≤ n), 0 < k →
      (∑ i : Fin k,
        Tusnady.sign (χ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) •
          v ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) ∈ K := by
  let w : ℕ → E := fun i => if hi : i < n then v ⟨i, hi⟩ else 0
  have hw : ∀ i, i < n → Allowed (w i) := by
    intro i hi
    simpa only [w, dif_pos hi] using hv ⟨i, hi⟩
  obtain ⟨ψ, hψ⟩ := prefix_signing_of_transform μ K Good Allowed T rules δ hδ hK n hn w hw
  refine ⟨fun i => ψ i.val, ?_⟩
  intro k hk hkpos
  have hp := hψ k hkpos hk
  rw [prefixSum, ← Fin.sum_univ_eq_sum_range] at hp
  have heq : (∑ i : Fin k, Tusnady.sign (ψ i.val) • w i.val) =
      ∑ i : Fin k, Tusnady.sign (ψ i.val) •
        v ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [w, dif_pos (lt_of_lt_of_le i.isLt hk)]
  exact heq ▸ hp

end Measure
end Tusnady.Upper
