import Tusnady.PrekopaFubini
import Tusnady.LiteratureGaussianAnderson

/-!
# Anderson's Gaussian shift inequality, without literature hypotheses

The functional midpoint theorem is proved by the layer-cake argument and
coordinate induction. The distance-penalty limit is taken in the source
space of every Gaussian linear image, covering singular images as well.
-/
noncomputable section
open MeasureTheory
namespace Tusnady.LiteratureProof

/-- The analytic interface is inhabited by an actual proved theorem. -/
theorem gaussianMidpointIntegralBound : LiteratureGaussian.GaussianMidpointIntegralBound := by
  intro n f g h hfc hgc hhc hfp hgp hhp C a hC ha hfB hgB hhB hmid
  apply Prekopa.gaussian_midpoint_integral_bound n f g h
    ⟨hfc, hfp, C, a, hC, ha, hfB⟩
    ⟨hgc, hgp, C, a, hC, ha, hgB⟩
    ⟨hhc, hhp, C, a, hC, ha, hhB⟩
  intro x y
  have heq : (fun i => (x i + y i) / 2) = LiteratureGaussian.midpoint x y := by
    funext i
    simp only [LiteratureGaussian.midpoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  exact hmid x y

/-- Exactly the Anderson premise used in the main proof, now discharged. -/
theorem anderson : Literature.Anderson :=
  LiteratureGaussian.anderson_of_midpoint gaussianMidpointIntegralBound

end Tusnady.LiteratureProof
