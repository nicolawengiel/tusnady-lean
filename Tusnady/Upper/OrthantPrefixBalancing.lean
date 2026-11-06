import Tusnady.Upper.OrthantPrefixTransfer
import Tusnady.Upper.PrefixBalancing

/-!
# Agreement of the finite and natural prefix conventions

These are exact changes of indexing.  They do not supply the still separate
Gaussian-measure monotonicity input in the signed-series argument.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Upper

variable {N : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Restricting a natural sequence and its Boolean signs gives exactly the
same finite prefix vector. -/
theorem finitePrefix_eq_prefixSum (V : Fin N → E) (v : ℕ → E)
    (hv : ∀ i : Fin N, v i.val = V i) (χ : ℕ → Bool) (k : Fin (N + 1)) :
    finitePrefix V (fun i => Tusnady.sign (χ i.val)) k = prefixSum v χ k.val := by
  rw [finitePrefix_eq_sum_fin, prefixSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hv ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ k.isLt)⟩]

/-- Positive finite prefixes together with the empty-prefix origin condition
control all our prefix cutoffs, using one fixed real sign coloring. -/
theorem real_finitePrefix_mem_of_fin_signs (V : Fin N → E) (χ : Fin N → Bool)
    (K : Set E) (hzero : (0 : E) ∈ K)
    (hprefix : ∀ k (hk : k ≤ N), 0 < k →
      (∑ i : Fin k,
        Tusnady.sign (χ ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) •
          V ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) ∈ K) :
    IsSignColoring (fun i => Tusnady.sign (χ i)) ∧
      ∀ k : Fin (N + 1), finitePrefix V (fun i => Tusnady.sign (χ i)) k ∈ K := by
  refine ⟨fun i => sign_is_sign (χ i), ?_⟩
  intro k
  by_cases hk : (k : ℕ) = 0
  · have hk0 : k = 0 := Fin.ext hk
    simpa only [hk0, finitePrefix_zero] using hzero
  · rw [finitePrefix_eq_sum_fin]
    exact hprefix k.val (Nat.le_of_lt_succ k.isLt) (Nat.pos_of_ne_zero hk)

end Tusnady.Upper
