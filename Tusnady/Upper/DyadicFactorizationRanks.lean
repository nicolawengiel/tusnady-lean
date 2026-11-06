import Tusnady.Definitions

/-!
# Coordinate ranks preserve all orthant incidences, including ties

The rank of a value is the number of input values at most it, minus one.
It need not be injective: repeated values intentionally share their rank.
Every closed threshold becomes an ordinary finite prefix cutoff.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Upper.DyadicFactorization

def coordinateRank {s N : ℕ} (P : Fin N → Point s) (i : Fin N) (j : Fin s) : ℕ := by
  classical
  exact (Finset.univ.filter (fun k => P k j ≤ P i j)).card - 1

def coordinateCut {s N : ℕ} (P : Fin N → Point s) (x : Point s) (j : Fin s) : Fin (N+1) := by
  classical
  refine ⟨(Finset.univ.filter (fun k => P k j ≤ x j)).card, ?_⟩
  exact Nat.lt_succ_of_le (by simpa using (Finset.card_le_univ
    (Finset.univ.filter (fun k => P k j ≤ x j))))

lemma coordinateRank_lt {s N : ℕ} (P : Fin N → Point s) (i : Fin N) (j : Fin s) :
    coordinateRank P i j < N := by
  classical
  have hpos : 0 < (Finset.univ.filter (fun k => P k j ≤ P i j)).card := by
    apply Finset.card_pos.mpr
    exact ⟨i, by simp⟩
  have hcard : (Finset.univ.filter (fun k => P k j ≤ P i j)).card ≤ N := by
    simpa using Finset.card_le_univ (Finset.univ.filter (fun k => P k j ≤ P i j))
  unfold coordinateRank
  omega

lemma coordinateRank_lt_cut_iff {s N : ℕ} (P : Fin N → Point s) (x : Point s)
    (i : Fin N) (j : Fin s) : coordinateRank P i j < coordinateCut P x j ↔ P i j ≤ x j := by
  classical
  let A := Finset.univ.filter (fun k => P k j ≤ P i j)
  let B := Finset.univ.filter (fun k => P k j ≤ x j)
  have hiA : i ∈ A := by simp [A]
  have ha : 0 < A.card := Finset.card_pos.mpr ⟨i, hiA⟩
  change A.card - 1 < B.card ↔ P i j ≤ x j
  by_cases hpx : P i j ≤ x j
  · have hsub : A ⊆ B := by
      intro k hk
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans hpx
    have hab := Finset.card_le_card hsub
    exact iff_of_true (by omega) hpx
  · have hsub : B ⊆ A := by
      intro k hk
      simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans (le_of_not_ge hpx)
    have hiB : i ∉ B := by simpa [B] using hpx
    have hne : B ≠ A := by
      intro heq
      exact hiB (heq ▸ hiA)
    have hcard := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    exact iff_of_false (by omega) hpx

lemma orthant_rank_iff {s N : ℕ} (P : Fin N → Point s) (x : Point s) (i : Fin N) :
    P i ∈ Anchored x ↔ ∀ j, coordinateRank P i j < coordinateCut P x j := by
  simp only [Anchored, Set.mem_setOf_eq, coordinateRank_lt_cut_iff]

end Tusnady.Upper.DyadicFactorization
