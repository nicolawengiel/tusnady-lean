import Tusnady.Upper.Ehrhard.CoordinateSections
import Tusnady.Upper.Ehrhard.ConvexLift

/-!
# Ehrhard's inequality for compact convex sets

The proof lifts two endpoint sets to heights zero and one, applies the proved
Gaussian section inequality, and identifies the intermediate section with the
actual weighted Minkowski mixture.  Ehrhard's inequality is a conclusion of
this file, never a hypothesis.  Endpoint masses are explicitly in (0,1).
-/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace OAI.GaussianPropeller
open Quantile EhrhardSmooth GaussianSections ConvexLift
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k+1))

/-- CDF form of the Gaussian Brunn--Minkowski inequality, with no requirement
that the intermediate probability itself be strictly between zero and one. -/
theorem compactConvex_gaussian_cdf_mixture
    (A B : Set E) (hAc : IsCompact A) (hBc : IsCompact B)
    (hAv : Convex ℝ A) (hBv : Convex ℝ B)
    (hAm : (gaussianMeasure (Fin k)).real A ∈ Ioo (0 : ℝ) 1)
    (hBm : (gaussianMeasure (Fin k)).real B ∈ Ioo (0 : ℝ) 1)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) :
    Φ (a * q ((gaussianMeasure (Fin k)).real A) +
      c * q ((gaussianMeasure (Fin k)).real B)) ≤
      (gaussianMeasure (Fin k)).real (mixture A B a c) := by
  have hAne : A.Nonempty := nonempty_of_measureReal_ne_zero hAm.1.ne'
  have hBne : B.Nonempty := nonempty_of_measureReal_ne_zero hBm.1.ne'
  let K : Set E' := splitEquiv ⁻¹' lift A B
  have hKc : IsClosed K := (isClosed_lift hAc hBc).preimage splitEquiv.continuous
  have hKv : Convex ℝ K := (convex_lift hAv hBv).linear_preimage splitEquiv.toLinearMap
  have hliftMeas : MeasurableSet (lift A B) := (isClosed_lift hAc hBc).measurableSet
  have hp0 : sectionProbability K (CoordinateProjection.projection keepFront) (append (0 : E) 0) =
      (gaussianMeasure (Fin k)).real A := by
    rw [sectionProbability_front (lift A B) hliftMeas, section_zero A B hBne]
  have hp1 : sectionProbability K (CoordinateProjection.projection keepFront) (append (0 : E) 1) =
      (gaussianMeasure (Fin k)).real B := by
    rw [sectionProbability_front (lift A B) hliftMeas, section_one A B hAne]
  have heqpoint : a • append (0 : E) 0 + c • append (0 : E) 1 = append (0 : E) c := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [append]
  have hm : sectionProbability K (CoordinateProjection.projection keepFront)
      (a • append (0 : E) 0 + c • append (0 : E) 1) =
      (gaussianMeasure (Fin k)).real (mixture A B a c) := by
    rw [heqpoint, sectionProbability_front (lift A B) hliftMeas]
    congr 1
    ext z
    exact mem_lift_at_weights A B z ha hc hac
  have h := closedConvexProbability_projection_cdf_concavity K hKc hKv keepFront
    (append (0 : E) 0) (append (0 : E) 1) ha hc hac
    (by simpa only [hp0] using hAm) (by simpa only [hp1] using hBm)
  simpa only [hp0, hp1, hm] using h

/-- Finite-quantile form of the same proved inequality. -/
theorem compactConvex_gaussian_quantile_mixture
    (A B : Set E) (hAc : IsCompact A) (hBc : IsCompact B)
    (hAv : Convex ℝ A) (hBv : Convex ℝ B)
    (hAm : (gaussianMeasure (Fin k)).real A ∈ Ioo (0 : ℝ) 1)
    (hBm : (gaussianMeasure (Fin k)).real B ∈ Ioo (0 : ℝ) 1)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1)
    (hMm : (gaussianMeasure (Fin k)).real (mixture A B a c) ∈ Ioo (0 : ℝ) 1) :
    a * q ((gaussianMeasure (Fin k)).real A) + c * q ((gaussianMeasure (Fin k)).real B) ≤
      q ((gaussianMeasure (Fin k)).real (mixture A B a c)) := by
  apply strictMono_Φ.le_iff_le.mp
  rw [Φ_q hMm]
  exact compactConvex_gaussian_cdf_mixture A B hAc hBc hAv hBv hAm hBm ha hc hac

end OAI.GaussianPropeller
