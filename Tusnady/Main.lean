import Tusnady.HereditaryConstruction
import Tusnady.FinalTransfer

/-!
# The higher-dimensional Tusnády lower bound

The exact target from Main.pdf Theorem 1.1 follows from the proved actual
depth construction and the proved exact-cardinality logarithmic transfer.
The only external mathematical premises are the five named general
literature statements in Literature.Assumptions.
-/
noncomputable section
namespace Tusnady

/-- Main.pdf Theorem 1.1, under the explicitly documented literature
premises. There is no additional construction or remainder hypothesis. -/
theorem main_lower_bound (literature : Literature.Assumptions) : HigherDimensionalLowerBound := by
  intro d hd
  obtain ⟨c,C,hc,hC,hmin,hconstruction⟩ := depth_construction_hereditary literature d hd
  exact lower_bound_from_depth_construction d hd c C hc hC hmin hconstruction

end Tusnady
