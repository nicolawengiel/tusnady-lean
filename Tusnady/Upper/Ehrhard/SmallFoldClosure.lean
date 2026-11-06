import Tusnady.Upper.Ehrhard.FoldRotation
import Tusnady.Upper.Ehrhard.ModifiedFoldContainment
import Tusnady.Upper.PrefixGaussianOneDimensional
import Tusnady.Upper.PrefixSmallRadius

/-!
# Closing the small-radius analytic goal from the vertical measure comparison

All orthogonal changes of coordinates, degenerate dimensions and the original
concrete signing fold are handled here.  The displayed vertical comparison
is supplied by the completed argument in `VerticalFoldMonotonicity`.
-/
noncomputable section
open Set MeasureTheory
namespace OAI.GaussianPropeller
open Tusnady.Upper GaussianSections ModifiedVerticalFold ModifiedFoldContainment

theorem smallGaussianFoldMonotonicity_of_vertical
    (hvertical : ∀ k : ℕ, 0 < k →
      ∀ K : Set (EuclideanSpace ℝ (Fin (k+1))), IsCompact K → Convex ℝ K →
      (1 : ℝ)/2 ≤ (gaussianMeasure (Fin (k+1))).real K →
      ∀ r : ℝ, 0 < r → r ≤ (1 : ℝ)/1000 →
      (gaussianMeasure (Fin (k+1))).real K ≤
        (gaussianMeasure (Fin (k+1))).real (gaussianVerticalFold K r)) :
    SmallGaussianFoldMonotonicity := by
  intro k K hKcomp hKconv hKsymm u hu hmass
  rcases k with _ | k
  · exact gaussianFold_mass_dimension_zero K u
  rcases k with _ | k
  · exact gaussianFold_mass_dimension_one K hKcomp hKconv hKsymm hmass u (by linarith)
  by_cases hu0 : u = 0
  · subst u
    exact gaussianFold_mass_zero _ K
  obtain ⟨e, he⟩ := exists_isometry_to_axis u
  let L := e '' K
  have hLcomp : IsCompact L := hKcomp.image e.continuous
  have hLconv : Convex ℝ L := hKconv.linear_image e.toLinearEquiv.toLinearMap
  have hLmass : (1 : ℝ)/2 ≤ (gaussianMeasure (Fin (k+1+1))).real L := by
    rw [gaussianMeasure_real_image_isometry e K hKcomp]
    exact hmass
  have hnorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hmono := hvertical (k+1) (by omega) L hLcomp hLconv hLmass ‖u‖ hnorm hu
  have hsubset := gaussianVerticalFold_subset_signingFold L hLcomp hLconv hnorm
  have hfoldmass := gaussianMeasure_real_image_isometry e (signingFold u K)
    (isCompact_signingFold K hKcomp u)
  have himage : e '' signingFold u K = signingFold (axis ‖u‖) L := by
    have h := image_signingFold e.toLinearEquiv K u
    change e '' signingFold u K = signingFold (e u) L at h
    simpa only [he] using h
  rw [himage] at hfoldmass
  change (gaussianMeasure (Fin (k+1+1))).real K ≤
    (gaussianMeasure (Fin (k+1+1))).real (signingFold u K)
  calc
    _ = (gaussianMeasure (Fin (k+1+1))).real L :=
      (gaussianMeasure_real_image_isometry e K hKcomp).symm
    _ ≤ _ := hmono
    _ ≤ (gaussianMeasure (Fin (k+1+1))).real (signingFold (axis ‖u‖) L) := measureReal_mono hsubset
    _ = _ := hfoldmass

end OAI.GaussianPropeller
