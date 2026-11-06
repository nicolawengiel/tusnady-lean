import Tusnady.Upper.Ehrhard.PlanarReductionData
import Tusnady.Upper.Ehrhard.PlanarFoldComparison
import Tusnady.Upper.Ehrhard.ModifiedFoldSymmetrization
import Tusnady.Upper.Ehrhard.SmallFoldClosure

/-!
# Proved small-radius Banaszczyk fold monotonicity

The actual first symmetrization inequality, the exact second-symmetrization
identity and the proved planar comparison are assembled.  Orthogonal
invariance then gives the original concrete signing fold in every dimension.
There is no literature or fold-monotonicity premise in the final theorem.
-/
noncomputable section
open MeasureTheory Set
namespace OAI.GaussianPropeller
open GaussianSections Symmetrization PlanarSymmetrization ModifiedVerticalFold
open ModifiedFoldPlanar PlanarReductionData PlanarFoldComparison

theorem gaussian_verticalFold_mass_mono_small {k : ℕ} (hk : 0 < k)
    (K : Set (EuclideanSpace ℝ (Fin (k+1)))) (hKcomp : IsCompact K) (hKconv : Convex ℝ K)
    (hKmass : (1 : ℝ)/2 ≤ (gaussianMeasure (Fin (k+1))).real K)
    {r : ℝ} (hr : 0 < r) (hsmall : r ≤ (1 : ℝ)/1000) :
    (gaussianMeasure (Fin (k+1))).real K ≤
      (gaussianMeasure (Fin (k+1))).real (gaussianVerticalFold K r) := by
  obtain ⟨hdata, _⟩ := actual_smallRadius_planarData hk K hKcomp hKconv hKmass hr hsmall
  have hplane := gaussian_mass_fold_ge_of_finite_section (reductionSet K)
    hdata.closed hdata.convex hdata.lower hdata.mass r hr hsmall
    (endpointAt K (Quantile.q (intervalMass r))) hdata.section_cap
  have hpr : intervalMass r ∈ Ioo (0 : ℝ) 1 :=
    (SmallRadiusQuantile.small_radius_quantile hr hsmall).1
  calc
    _ = (gaussianMeasure (Fin 2)).real (reductionSet K) :=
      (PlanarSymmetrizationData.gaussian_mass_twice K hKcomp.isClosed.measurableSet).symm
    _ ≤ _ := hplane
    _ = (gaussianMeasure (Fin (k+1))).real (gaussianVerticalFold (symmetrization K) r) :=
      gaussian_mass_fold_planarSymmetrization K hKcomp.isClosed hr.le hpr
    _ ≤ _ := gaussian_fold_symmetrization_mass_le K hKcomp hKconv hr

/-- The analytic small-radius input is now actually proved.  Dimensions zero
and one, zero vectors, and arbitrary directions are included by the proved
closure theorem.  This declaration has no additional theorem hypothesis. -/
theorem small_gaussian_fold_monotonicity : Tusnady.Upper.SmallGaussianFoldMonotonicity := by
  apply smallGaussianFoldMonotonicity_of_vertical
  intro k hk K hKcomp hKconv hKmass r hr hsmall
  exact gaussian_verticalFold_mass_mono_small hk K hKcomp hKconv hKmass hr hsmall

end OAI.GaussianPropeller
