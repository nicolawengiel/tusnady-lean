import Tusnady.Upper.OrthantPrefixTransfer
import Tusnady.Upper.DyadicFactorization

/-!
# The proved projected factorization in the prefix transfer

The finite dyadic geometry and the sorting geometry are assembled here.
This result is unconditional.  Producing signs with all required prefix
inner-product bounds is a separate analytic step and is not claimed here.
-/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Tusnady.Upper
attribute [local instance] Classical.propDecidable
open DyadicFactorization

/-- The first coordinates of the point sequence after sorting by its last one. -/
def projectedPoints {s N : ℕ} (P : Fin N → Point (s + 1)) : Fin N → Point s :=
  fun i => frontPoint (P (lastSort P i))

/-- Actual finite dyadic rows and columns reconstruct every full orthant sum
as a signed prefix in one common Euclidean space. -/
theorem exists_projected_prefix_factorization {s N : ℕ} (P : Fin N → Point (s + 1)) :
    ∃ k : ℕ,
    ∃ U : Query s N → EuclideanSpace ℝ (Fin k),
    ∃ V : Fin N → EuclideanSpace ℝ (Fin k),
      (∀ i, ‖V i‖ ≤ 1) ∧
      (∀ q, ‖U q‖ ≤ factorConstant s * (Real.log ((N : ℝ) + 2))^s) ∧
      (∀ χ : Fin N → ℝ, ∀ x : Point (s + 1),
        realAnchoredCount (fun i => P (lastSort P i)) χ x =
          inner ℝ (U (coordinateCut (projectedPoints P) (frontPoint x)))
            (finitePrefix V χ (lastCut P x))) := by
  obtain ⟨k, U, V, hV, hU, hfactor⟩ := exists_orthant_factorization (projectedPoints P)
  refine ⟨k, U, V, hV, hU, ?_⟩
  intro χ x
  exact sorted_count_eq_inner_prefix P U V (coordinateCut (projectedPoints P)) hfactor χ x

/-- For the proved dyadic factorization, the remaining sign-selection input is
stated for every finite row family and every prefix.  Its type is explicit;
this implication does not postulate or prove that analytic input. -/
theorem coloring_of_dyadic_prefix_signing {s N : ℕ} (P : Fin N → Point (s + 1)) (B : ℝ)
    (hsigning : ∀ k : ℕ,
      ∀ U : Query s N → EuclideanSpace ℝ (Fin k),
      ∀ V : Fin N → EuclideanSpace ℝ (Fin k),
      (∀ i, ‖V i‖ ≤ 1) →
      (∀ q, ‖U q‖ ≤ factorConstant s * (Real.log ((N : ℝ) + 2))^s) →
      ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
        ∀ q (m : Fin (N + 1)), |inner ℝ (U q) (finitePrefix V χ m)| ≤ B) :
    ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
      ∀ x : Point (s + 1), |realAnchoredCount P χ x| ≤ B := by
  obtain ⟨k, U, V, hV, hU, hcount⟩ := exists_projected_prefix_factorization P
  obtain ⟨χ, hχ, hpref⟩ := hsigning k U V hV hU
  apply coloring_bound_of_reindex P (lastSort P) χ hχ B
  intro x
  rw [hcount χ x]
  exact hpref _ _

end Tusnady.Upper
