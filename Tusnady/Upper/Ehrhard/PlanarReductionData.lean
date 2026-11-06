import Tusnady.Upper.Ehrhard.PlanarSymmetrizationData
import Tusnady.Upper.Ehrhard.PlanarSupport
import Tusnady.Upper.Ehrhard.PlanarCap

/-!
# Actual planar data at the fold cutoff

Every property below is derived for the actual two-stage symmetrization of a
compact convex Gaussian-large input.  The structure is an output package with
a proved inhabitant, not an additional assumption or literature interface.
-/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace OAI.GaussianPropeller.PlanarReductionData
open Quantile GaussianSections Symmetrization PlanarSymmetrization
open PlanarSymmetrizationData ModifiedVerticalFold

variable {k : ℕ}
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

def reductionSet (K : Set E') : Set Plane := planarSymmetrization (symmetrization K)
def endpointAt (K : Set E') (τ : ℝ) : ℝ := q (horizontalMass (symmetrization K) τ)

structure PlanarData (L : Set Plane) (τ a₀ : ℝ) : Prop where
  closed : IsClosed L
  convex : Convex ℝ L
  lower : PlanarCap.LowerClosed L
  mass : (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin 2)).real L
  endpoint_nonneg : 0 ≤ a₀
  section_support : PlanarSupport.horizontalSection L τ = Iic a₀
  section_cap : PlanarCap.horizontalSection L τ = Iic a₀

theorem actual_planarData (hk : 0 < k) (K : Set E') (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKm : (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin (k + 1))).real K)
    (τ : ℝ) (hτ : τ ≤ 0) : PlanarData (reductionSet K) τ (endpointAt K τ) := by
  have hp := horizontalMass_nonpositive_mem hk K hKc hKv hKm τ hτ
  refine
    { closed := isClosed_planarSymmetrization _ (isClosed_symmetrization K hKc.isClosed)
      convex := convex_planarSymmetrization_symmetrization hk K hKc hKv
      lower := ?_
      mass := ?_
      endpoint_nonneg := endpoint_nonnegative hk K hKc hKv hKm τ hτ
      section_support := ?_
      section_cap := ?_ }
  · intro x y hx hxy
    exact twice_lower K x hx y hxy
  · change (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin 2)).real (planarSymmetrization (symmetrization K))
    rwa [gaussian_mass_twice K hKc.isClosed.measurableSet]
  · ext x
    change Φ x ≤ horizontalMass (symmetrization K) τ ↔ x ≤ q (horizontalMass (symmetrization K) τ)
    simpa only [Φ_q hp] using
      (strictMono_Φ.le_iff_le : Φ x ≤ Φ (q (horizontalMass (symmetrization K) τ)) ↔
        x ≤ q (horizontalMass (symmetrization K) τ))
  · ext x
    change Φ x ≤ horizontalMass (symmetrization K) τ ↔ x ≤ q (horizontalMass (symmetrization K) τ)
    simpa only [Φ_q hp] using
      (strictMono_Φ.le_iff_le : Φ x ≤ Φ (q (horizontalMass (symmetrization K) τ)) ↔
        x ≤ q (horizontalMass (symmetrization K) τ))

/-- Adapter for the explicit-binder interface of `PlanarSupport`. -/
theorem PlanarData.lower_support {L : Set Plane} {τ a₀ : ℝ} (h : PlanarData L τ a₀) :
    ∀ x ∈ L, ∀ z : Plane, (∀ i, z i ≤ x i) → z ∈ L := by
  intro x hx z hz
  exact h.lower hx hz

/-- All actual small-radius planar inputs, with the strict negative cutoff
verified from the proved scalar Gaussian interval bounds. -/
theorem actual_smallRadius_planarData (hk : 0 < k) (K : Set E') (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKm : (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin (k + 1))).real K)
    {r : ℝ} (hr : 0 < r) (hsmall : r ≤ (1 : ℝ) / 1000) :
    PlanarData (reductionSet K) (q (intervalMass r)) (endpointAt K (q (intervalMass r))) ∧
      Φ (q (intervalMass r)) < (1 : ℝ) / 2 := by
  have hp : intervalMass r ∈ Ioo (0 : ℝ) 1 := (SmallRadiusQuantile.small_radius_quantile hr hsmall).1
  have hphalf : intervalMass r < (1 : ℝ) / 2 := by
    have hle : intervalMass r ≤ r := SmallRadiusQuantile.intervalMass_le_radius hr.le
    linarith
  have hτ : q (intervalMass r) < 0 := by
    apply strictMono_Φ.lt_iff_lt.mp
    rwa [Φ_q hp, Φ_zero]
  exact ⟨actual_planarData hk K hKc hKv hKm _ hτ.le, by rwa [Φ_q hp]⟩

end OAI.GaussianPropeller.PlanarReductionData
