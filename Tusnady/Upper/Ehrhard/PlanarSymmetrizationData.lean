import Tusnady.Upper.Ehrhard.ModifiedFoldPlanar
import Tusnady.Upper.Ehrhard.GaussianConvexOrigin

/-!
# Concrete planar data for the final fold comparison

The actual two-stage symmetrization is a closed convex lower set of the same
Gaussian mass.  In positive horizontal dimension its section at any nonpositive
height has probability in `[1/2,1)` whenever the initial compact convex set has
mass at least half.  Thus its finite horizontal endpoint is nonnegative.
-/

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace OAI.GaussianPropeller.PlanarSymmetrizationData
open Quantile GaussianSections Symmetrization PlanarSymmetrization ModifiedFoldPlanar
variable {k : ℕ}
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem gaussian_mass_twice (K : Set E') (hK : MeasurableSet K) :
    (gaussianMeasure (Fin 2)).real (planarSymmetrization (symmetrization K)) =
      (gaussianMeasure (Fin (k + 1))).real K :=
  (gaussian_mass_planarSymmetrization _ (measurableSet_symmetrization hK)).trans
    (gaussian_mass_symmetrization K hK)

theorem twice_lower (K : Set E') :
    ∀ x ∈ planarSymmetrization (symmetrization K), ∀ z : Plane,
      (∀ i, z i ≤ x i) → z ∈ planarSymmetrization (symmetrization K) := by
  intro x hx z hz
  change Φ (z 0) ≤ horizontalMass (symmetrization K) (z 1)
  exact ((strictMono_Φ.monotone (hz 0)).trans hx).trans
    (horizontalMass_symmetrization_antitone K (hz 1))

theorem twice_zero_mem (hk : 0 < k) (K : Set E') (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKm : (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin (k + 1))).real K) :
    (0 : Plane) ∈ planarSymmetrization (symmetrization K) := by
  apply closedConvex_zero_mem_of_half_gaussianMass _
    (isClosed_planarSymmetrization _ (isClosed_symmetrization K hKc.isClosed))
    (convex_planarSymmetrization_symmetrization hk K hKc hKv)
  rwa [gaussian_mass_twice K hKc.isClosed.measurableSet]

theorem horizontalMass_nonpositive_ge_half (hk : 0 < k) (K : Set E')
    (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKm : (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin (k + 1))).real K)
    (τ : ℝ) (hτ : τ ≤ 0) :
    (1 : ℝ) / 2 ≤ horizontalMass (symmetrization K) τ := by
  have hz := twice_zero_mem hk K hKc hKv hKm
  have hzero : (1 : ℝ) / 2 ≤ horizontalMass (symmetrization K) 0 := by
    change Φ ((0 : Plane) 0) ≤ horizontalMass (symmetrization K) ((0 : Plane) 1) at hz
    simpa only [PiLp.zero_apply, Φ_zero] using hz
  exact hzero.trans (horizontalMass_symmetrization_antitone K hτ)

theorem horizontalMass_nonpositive_mem (hk : 0 < k) (K : Set E')
    (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKm : (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin (k + 1))).real K)
    (τ : ℝ) (hτ : τ ≤ 0) :
    horizontalMass (symmetrization K) τ ∈ Ioo (0 : ℝ) 1 :=
  ⟨(by linarith [horizontalMass_nonpositive_ge_half hk K hKc hKv hKm τ hτ]),
    horizontalMass_symmetrization_lt_one hk K hKc τ⟩

theorem endpoint_nonnegative (hk : 0 < k) (K : Set E') (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKm : (1 : ℝ) / 2 ≤ (gaussianMeasure (Fin (k + 1))).real K)
    (τ : ℝ) (hτ : τ ≤ 0) :
    0 ≤ q (horizontalMass (symmetrization K) τ) := by
  apply strictMono_Φ.le_iff_le.mp
  rw [Φ_zero, Φ_q (horizontalMass_nonpositive_mem hk K hKc hKv hKm τ hτ)]
  exact horizontalMass_nonpositive_ge_half hk K hKc hKv hKm τ hτ

theorem cdf_sublevel_eq_Iic (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    {x : ℝ | Φ x ≤ p} = Iic (q p) := by
  ext x
  change Φ x ≤ p ↔ x ≤ q p
  simpa only [Φ_q hp] using (strictMono_Φ.le_iff_le : Φ x ≤ Φ (q p) ↔ x ≤ q p)

end OAI.GaussianPropeller.PlanarSymmetrizationData
