import Tusnady.Upper.DyadicFactorizationRanks
import Tusnady.Upper.DyadicFactorizationTensor
import Tusnady.Upper.DyadicFactorizationLog

/-!
# Explicit Euclidean factorization of finite orthant incidences

This proves the factorization needed in Nikolov, Mathematika 63 (2017),
Lemma 7 and the proof of Theorem 1 in §4, without using a gamma-two norm.
The indexed input may have repetitions.  Every closed orthant is represented,
including its empty trace, by one of `(N+1)^s` coordinate cutoffs.

The column norms are at most one and the row norms are at most
`(3 / log 2)^s * log(N+2)^s`.  The constant depends only on the dimension.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Tusnady.Upper.DyadicFactorization
attribute [local instance] Classical.propDecidable

abbrev Query (s N : ℕ) := Fin s → Fin (N+1)
abbrev FactorSpace (s N : ℕ) := EuclideanSpace ℝ (TensorFeature s (depth N))

lemma query_card (s N : ℕ) : Fintype.card (Query s N) = (N+1)^s := by simp [Query]

def pointVector {s N : ℕ} (P : Fin N → Point s) (i : Fin N) : FactorSpace s N :=
  normalizedColumn (depth N) (coordinateRank P i)

def queryVector {s N : ℕ} (q : Query s N) : FactorSpace s N :=
  normalizedRow (depth N) (fun j => (q j).val)

lemma pointVector_norm_le {s N : ℕ} (P : Fin N → Point s) (i : Fin N) :
    ‖pointVector P i‖ ≤ 1 := by
  exact normalizedColumn_norm_le _ _ fun j => (coordinateRank_lt P i j).trans (depth_large N)

lemma queryVector_norm_le {s N : ℕ} (q : Query s N) :
    ‖queryVector q‖ ≤ factorConstant s * (Real.log ((N : ℝ)+2))^s := by
  calc
    _ ≤ ((depth N+1 : ℕ) : ℝ)^s :=
      normalizedRow_norm_le _ _ (fun j => (Nat.le_of_lt_succ (q j).isLt).trans (depth_large N).le)
    _ ≤ _ := depth_pow_log_bound s N

lemma query_inner_point {s N : ℕ} (P : Fin N → Point s) (q : Query s N) (i : Fin N) :
    inner ℝ (queryVector q) (pointVector P i) =
      if ∀ j, coordinateRank P i j < q j then 1 else 0 := by
  exact normalized_inner _ _ _
    (fun j => (Nat.le_of_lt_succ (q j).isLt).trans (depth_large N).le)
    (fun j => (coordinateRank_lt P i j).trans (depth_large N))

lemma query_orthant_inner {s N : ℕ} (P : Fin N → Point s) (x : Point s) (i : Fin N) :
    inner ℝ (queryVector (coordinateCut P x)) (pointVector P i) =
      if P i ∈ Anchored x then 1 else 0 := by
  rw [query_inner_point]
  simp only [← orthant_rank_iff]

/-- The finite Euclidean factorization with a conventional `Fin k` ambient index.
No injectivity or general-position assumption on the input sequence is needed. -/
theorem exists_orthant_factorization {s N : ℕ} (P : Fin N → Point s) :
    ∃ k : ℕ,
    ∃ U : Query s N → EuclideanSpace ℝ (Fin k),
    ∃ V : Fin N → EuclideanSpace ℝ (Fin k),
      (∀ i, ‖V i‖ ≤ 1) ∧
      (∀ q, ‖U q‖ ≤ factorConstant s * (Real.log ((N : ℝ)+2))^s) ∧
      (∀ x i, inner ℝ (U (coordinateCut P x)) (V i) =
        if P i ∈ Anchored x then 1 else 0) := by
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Fintype.equivFin (TensorFeature s (depth N)))
  refine ⟨Fintype.card (TensorFeature s (depth N)),
    (fun q => e (queryVector q)), (fun i => e (pointVector P i)), ?_, ?_, ?_⟩
  · intro i
    simpa only [e.norm_map] using pointVector_norm_le P i
  · intro q
    simpa only [e.norm_map] using queryVector_norm_le q
  · intro x i
    simpa only [e.inner_map_map] using query_orthant_inner P x i

end Tusnady.Upper.DyadicFactorization
