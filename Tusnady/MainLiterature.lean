import Tusnady.Main
import Tusnady.LiteratureAnderson
import Tusnady.LiteratureGaussianSidak
import Tusnady.LiteratureEntropyChain

/-!
The second-stage intermediate main theorem: four literature premises have
been discharged. Sampling remains explicit until its proof is complete.
This is not the unconditional completion target.
-/
namespace Tusnady

/-- The original main conclusion with exactly the one still open premise. -/
theorem main_lower_bound_of_sampling (sampling : Literature.Sampling) :
    HigherDimensionalLowerBound :=
  main_lower_bound {
    sidak := LiteratureProof.sidak
    anderson := LiteratureProof.anderson
    sampling := sampling
    entropyChain := LiteratureProof.conditionalEntropyChainIdentity
    rosenblatt := LiteratureProof.rosenblattUniform
  }

end Tusnady
