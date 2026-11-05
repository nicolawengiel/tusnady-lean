import Tusnady.MainLiterature
import Tusnady.MainWitness
import Tusnady.LiteratureSamplingTheorem

/-!
# The higher-dimensional main theorem without literature premises

All five unchanged literature propositions are inhabited by proved terms.
The original discrepancy conclusion and its explicit real-coloring witness
version therefore have no remaining literature or construction parameters.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady

/-- All five original literature propositions, now proved. -/
theorem LiteratureProof.assumptionsProved : Literature.Assumptions where
  sidak := LiteratureProof.sidak
  anderson := LiteratureProof.anderson
  sampling := LiteratureProof.sampling
  entropyChain := LiteratureProof.conditionalEntropyChainIdentity
  rosenblatt := LiteratureProof.rosenblattUniform

/-- Main.pdf Theorem 1.1, with no unproved literature premises. -/
theorem main_lower_bound_unconditional : HigherDimensionalLowerBound :=
  main_lower_bound LiteratureProof.assumptionsProved

/-- Exact N distinct points, chosen before every real sign coloring.
The constants precede N and may depend only on the fixed dimension. -/
theorem main_lower_bound_real_colorings_unconditional :
    ∀ d : ℕ, 3 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∃ P : Fin N → Point d,
        Function.Injective P ∧ (Finset.univ.image P).card = N ∧
        ∀ χ : Fin N → ℝ, IsSignColoring χ →
          ∃ x : Point d,
            c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
              |∑ i ∈ trace P x, χ i| :=
  main_lower_bound_real_colorings LiteratureProof.assumptionsProved

end Tusnady
