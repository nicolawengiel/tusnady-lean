import Tusnady.LiteratureGaussianPenalty

/-!
# Anderson from the separately proved Gaussian-dominated midpoint theorem

This module discharges all Gaussian, linear-image, distance-penalty,
symmetry, and limiting steps. `GaussianMidpointIntegralBound` is the
explicit analytic intermediate interface which the independent Prékopa
modules prove in `LiteratureAnderson`; it is not a new literature assumption
or global axiom.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.LiteratureGaussian
open MeasureTheory Set Metric Filter
open scoped BigOperators Topology

/-- The analytic intermediate theorem proved by the Prékopa modules and
inhabited by `LiteratureProof.gaussianMidpointIntegralBound`. -/
def GaussianMidpointIntegralBound : Prop :=
  ∀ k : ℕ, ∀ f g h : (Fin k → ℝ) → ℝ,
    Continuous f → Continuous g → Continuous h →
    (∀ x, 0 < f x) → (∀ x, 0 < g x) → (∀ x, 0 < h x) →
    ∀ C a : ℝ, 0 < C → 0 < a →
    (∀ x, f x ≤ C*Real.exp (-a*∑ i, (x i)^2)) →
    (∀ x, g x ≤ C*Real.exp (-a*∑ i, (x i)^2)) →
    (∀ x, h x ≤ C*Real.exp (-a*∑ i, (x i)^2)) →
    (∀ x y, f x*g y ≤ h (midpoint x y)^2) →
    (∫ x, f x)*(∫ x, g x) ≤ (∫ x, h x)^2

theorem integral_penalty_shift_le (hPL : GaussianMidpointIntegralBound) {k n : ℕ}
    (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (c : Fin n → ℝ) :
    (∫ x, penalty N A K c x) ≤ ∫ x, penalty N A K 0 x := by
  have h := hPL k (penalty N A K c) (penalty N A K (-c)) (penalty N A K 0)
    (penalty_continuous _ _ _ _) (penalty_continuous _ _ _ _) (penalty_continuous _ _ _ _)
    (penalty_pos _ _ _ _) (penalty_pos _ _ _ _) (penalty_pos _ _ _ _)
    (Real.exp (-gaussianEntropyConstant k)) (1/2) (Real.exp_pos _) (by norm_num)
    (penalty_gaussian_bound _ _ _ _) (penalty_gaussian_bound _ _ _ _) (penalty_gaussian_bound _ _ _ _)
    (penalty_midpoint_product N A K hK hconv hne c)
  rw [integral_penalty_neg N A K hsymm c] at h
  have hpos : 0 ≤ ∫ x, penalty N A K 0 x := integral_nonneg fun x => (penalty_pos _ _ _ _ x).le
  nlinarith

/-- Full source-space shift inequality, for arbitrary finite continuous
linear maps including zero and singular maps. -/
theorem linearImage_anderson (hPL : GaussianMidpointIntegralBound) {k n : ℕ}
    (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (c : Fin n → ℝ) :
    Literature.standardGaussian k {x : Fin k → ℝ | A x-c ∈ K} ≤
      Literature.standardGaussian k {x : Fin k → ℝ | A x ∈ K} := by
  classical
  by_cases hne : K.Nonempty
  · have hc : MeasurableSet {x : Fin k → ℝ | A x-c ∈ K} :=
      hK.measurableSet.preimage (A.measurable.sub measurable_const)
    have h0 : MeasurableSet {x : Fin k → ℝ | A x ∈ K} := hK.measurableSet.preimage A.measurable
    rw [gaussianConditioningMass_eq_gaussian_measure k hc,
      gaussianConditioningMass_eq_gaussian_measure k h0]
    apply ENNReal.ofReal_le_ofReal
    have hle := le_of_tendsto_of_tendsto
      (integral_penalty_tendsto A K hK hne c) (integral_penalty_tendsto A K hK hne 0)
      (Filter.Eventually.of_forall (fun N => integral_penalty_shift_le hPL N A K hK hconv hne hsymm c))
    simpa only [sub_zero,gaussianConditioningMass,exponentialEventMass,standardGaussianDensity] using hle
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hKe]

/-- Exactly the current declared `Literature.Anderson`, with every
Gaussian/degeneracy step proved. `LiteratureAnderson` supplies the proved
Prékopa intermediate and exports the theorem without this parameter. -/
theorem anderson_of_midpoint (hPL : GaussianMidpointIntegralBound) : Literature.Anderson := by
  intro n μ hμ K hK hconv hsymm c
  obtain ⟨k,B,rfl⟩ := hμ
  let A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) := B.mulVecLin.toContinuousLinearMap
  change ((Literature.standardGaussian k).map A) {x | x-c ∈ K} ≤
    ((Literature.standardGaussian k).map A) K
  have hS : MeasurableSet {x : Fin n → ℝ | x-c ∈ K} :=
    hK.measurableSet.preimage (measurable_id.sub measurable_const)
  rw [Measure.map_apply A.measurable hS,
    Measure.map_apply A.measurable hK.measurableSet]
  exact linearImage_anderson hPL A K hK hconv hsymm c

end Tusnady.LiteratureGaussian
