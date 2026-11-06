import Tusnady.Upper.Ehrhard.ModifiedVerticalFold
import Tusnady.Upper.Ehrhard.GaussianScalar
import Tusnady.Upper.Ehrhard.SmallRadiusQuantile

/-!
# First symmetrization step for the modified Gaussian fold

This proves Szusterman's first reduction by applying the proved scalar Gaussian
isoperimetry separately to every retained compact convex vertical fiber, then
integrating the actual probabilities by Fubini.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Pointwise RealInnerProductSpace
namespace OAI.GaussianPropeller.ModifiedVerticalFold
open Quantile GaussianSections Symmetrization
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k+1))

theorem vertical_fold_symmetrization_mass_le
    (K : Set E') (hKcomp : IsCompact K) (hKconv : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) (y : E) :
    (gaussianReal 0 1).real (verticalSection (gaussianVerticalFold (symmetrization K) r) y) ≤
      (gaussianReal 0 1).real (verticalSection (gaussianVerticalFold K r) y) := by
  rw [verticalSection_fold_symmetrization K hr.le, verticalSection_fold]
  by_cases hcut : intervalMass r ≤ sectionMass K y
  · rw [if_pos hcut, if_pos hcut]
    have hpos : 0 < sectionMass K y :=
      lt_of_lt_of_le (SmallRadiusQuantile.intervalMass_pos hr) hcut
    have hp : sectionMass K y ∈ Ioo (0 : ℝ) 1 :=
      ⟨hpos, sectionMass_lt_one_of_compact K hKcomp y⟩
    rw [gaussian_cdf_translated_sublevel_mass hp]
    exact real_closedConvex_gaussian_isoperimetry (verticalSection K y)
      (isClosed_verticalSection hKcomp.isClosed y) (convex_verticalSection K hKconv y) hp hr.le
  · simp only [if_neg hcut, measureReal_empty]
    exact le_refl _

/-- The first complete measure comparison: no Ehrhard or isoperimetry premise
remains, since those have been proved for the actual Gaussian measure. -/
theorem gaussian_fold_symmetrization_mass_le
    (K : Set E') (hKcomp : IsCompact K) (hKconv : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) :
    (gaussianMeasure (Fin (k+1))).real (gaussianVerticalFold (symmetrization K) r) ≤
      (gaussianMeasure (Fin (k+1))).real (gaussianVerticalFold K r) := by
  have hleft := measurableSet_gaussianVerticalFold (symmetrization K)
    (isClosed_symmetrization K hKcomp.isClosed) r
  have hright := measurableSet_gaussianVerticalFold K hKcomp.isClosed r
  rw [gaussianMeasure_real_sections _ hleft, gaussianMeasure_real_sections _ hright]
  exact integral_mono (integrable_verticalSection_mass _ hleft)
    (integrable_verticalSection_mass _ hright)
    (vertical_fold_symmetrization_mass_le K hKcomp hKconv hr)

end OAI.GaussianPropeller.ModifiedVerticalFold
