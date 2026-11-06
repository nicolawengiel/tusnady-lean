/-
Copyright (c) 2026 Zhewei Wei. Distributed under the MIT license.
See vendor/wei-6f14d177/LICENSE and provenance.json.
Source: wzskytop/tusnady-lean, commit 6f14d177668e79a9155f7cd60496313514ad0c9e.
Integration adaptation: local import module names are prefixed with `Wei`;
mathematical namespaces and proof bodies are unchanged.
-/
import Wei.Oscillation.R65

namespace Oscillation

/-- The all-n, all-colorings random-point lower bound through the direct proof. -/
theorem paper_lower_bound : Riesz.PaperLowerBound := R65.paper_lower_bound

/-- The deterministic planar rectangle-discrepancy consequence. -/
theorem planar_tusnady_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      c * (Real.logb 2 n) ^ (3 / 2 : ℝ) < Riesz.PointSets.Δ₂ n :=
  Riesz.deterministic_lower_of_paper paper_lower_bound

end Oscillation
