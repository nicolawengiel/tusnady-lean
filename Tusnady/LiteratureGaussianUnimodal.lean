import Tusnady.LiteratureGaussianAnderson
import Mathlib.Topology.Order.Compact

/-! Closed midpoint-convex scalar sections and Gaussian unimodality. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.LiteratureGaussian
open MeasureTheory Set Metric Filter
open scoped BigOperators Topology

/-- Closed midpoint-convex subsets of the real line contain the entire
interval between any two of their points. The proof uses extrema of the
two compact pieces, not a midpoint-convexity theorem as a new assumption. -/
theorem Icc_subset_of_closed_midpoint (S : Set ℝ) (hS : IsClosed S)
    (hmid : ∀ x ∈ S, ∀ y ∈ S, (x+y)/2 ∈ S) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S) :
    Icc a b ⊆ S := by
  intro x hx
  by_contra hxs
  let L := S ∩ Icc a x
  let R := S ∩ Icc x b
  have hLc : IsCompact L := isCompact_Icc.inter_left hS
  have hRc : IsCompact R := isCompact_Icc.inter_left hS
  have hLn : L.Nonempty := ⟨a,ha,le_rfl,hx.1⟩
  have hRn : R.Nonempty := ⟨b,hb,hx.2,le_rfl⟩
  let p := sSup L
  let q := sInf R
  have hp : p ∈ L := hLc.sSup_mem hLn
  have hq : q ∈ R := hRc.sInf_mem hRn
  have hpx : p < x := lt_of_le_of_ne hp.2.2 (by intro he; exact hxs (he ▸ hp.1))
  have hxq : x < q := lt_of_le_of_ne hq.2.1 (by intro he; exact hxs (he ▸ hq.1))
  have hm : (p+q)/2 ∈ S := hmid p hp.1 q hq.1
  by_cases hmx : (p+q)/2 ≤ x
  · have hmL : (p+q)/2 ∈ L := ⟨hm,by linarith [hp.2.1],hmx⟩
    have hmax : (p+q)/2 ≤ p := le_csSup hLc.bddAbove hmL
    linarith
  · have hmR : (p+q)/2 ∈ R := ⟨hm,le_of_not_ge hmx,by linarith [hq.2.2]⟩
    have hmin : q ≤ (p+q)/2 := csInf_le hRc.bddBelow hmR
    linarith

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureGaussian
open MeasureTheory Set Metric Filter
open scoped BigOperators Topology
variable {k n : ℕ}

lemma integral_penalty_midpoint (hPL : GaussianMidpointIntegralBound)
    (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (c d : Fin n → ℝ) :
    (∫ x, penalty N A K c x)*(∫ x, penalty N A K d x) ≤
      (∫ x, penalty N A K (midpoint c d) x)^2 :=
  hPL k (penalty N A K c) (penalty N A K d) (penalty N A K (midpoint c d))
    (penalty_continuous _ _ _ _) (penalty_continuous _ _ _ _) (penalty_continuous _ _ _ _)
    (penalty_pos _ _ _ _) (penalty_pos _ _ _ _) (penalty_pos _ _ _ _)
    (Real.exp (-gaussianEntropyConstant k)) (1/2) (Real.exp_pos _) (by norm_num)
    (penalty_gaussian_bound _ _ _ _) (penalty_gaussian_bound _ _ _ _) (penalty_gaussian_bound _ _ _ _)
    (penalty_midpoint_product_general N A K hK hconv hne c d)

/-- Full ray monotonicity of the actual Gaussian penalties, not merely a
maximum at zero. This is the section monotonicity needed for Šidák. -/
theorem integral_penalty_ray_antitone (hPL : GaussianMidpointIntegralBound)
    (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (c : Fin n → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫ x, penalty N A K (t • c) x) ≤ ∫ x, penalty N A K (s • c) x := by
  let F : ℝ → ℝ := fun r => ∫ x, penalty N A K (r • c) x
  have hF : Continuous F := (integral_penalty_continuous N A K).comp (continuous_id.smul continuous_const)
  have hFn : ∀ r, 0 ≤ F r := fun r => integral_nonneg fun x => (penalty_pos _ _ _ _ x).le
  have hFe : ∀ r, F (-r) = F r := by
    intro r
    change (∫ x, penalty N A K ((-r) • c) x) = _
    rw [neg_smul,integral_penalty_neg N A K hsymm]
  let S : Set ℝ := {r | F t ≤ F r}
  have hSc : IsClosed S := isClosed_le continuous_const hF
  have hSm : ∀ x ∈ S, ∀ y ∈ S, (x+y)/2 ∈ S := by
    intro x hx y hy
    have hgeom := integral_penalty_midpoint hPL N A K hK hconv hne (x • c) (y • c)
    have hid : midpoint (x • c) (y • c) = ((x+y)/2) • c := by
      ext i
      simp [midpoint]
      ring
    rw [hid] at hgeom
    change F x*F y ≤ F ((x+y)/2)^2 at hgeom
    have hprod : F t*F t ≤ F x*F y :=
      mul_le_mul hx hy (hFn t) ((hFn t).trans hx)
    change F t ≤ F ((x+y)/2)
    nlinarith [hFn t,hFn ((x+y)/2)]
  have hSt : t ∈ S := by change F t ≤ F t; exact le_rfl
  have hSnt : -t ∈ S := by change F t ≤ F (-t); rw [hFe]
  exact Icc_subset_of_closed_midpoint S hSc hSm hSnt hSt ⟨by linarith, hst⟩

/-- The actual Gaussian measure of a closed convex symmetric set is
nonincreasing along every nonnegative translation ray. Arbitrary singular
linear images are included directly by the source-space proof. -/
theorem linearImage_anderson_ray_le (hPL : GaussianMidpointIntegralBound)
    (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (c : Fin n → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    Literature.standardGaussian k {x : Fin k → ℝ | A x-t • c ∈ K} ≤
      Literature.standardGaussian k {x : Fin k → ℝ | A x-s • c ∈ K} := by
  classical
  by_cases hne : K.Nonempty
  · have htM : MeasurableSet {x : Fin k → ℝ | A x-t • c ∈ K} :=
      hK.measurableSet.preimage (A.measurable.sub measurable_const)
    have hsM : MeasurableSet {x : Fin k → ℝ | A x-s • c ∈ K} :=
      hK.measurableSet.preimage (A.measurable.sub measurable_const)
    rw [gaussianConditioningMass_eq_gaussian_measure k htM,
      gaussianConditioningMass_eq_gaussian_measure k hsM]
    apply ENNReal.ofReal_le_ofReal
    exact le_of_tendsto_of_tendsto
      (integral_penalty_tendsto A K hK hne (t • c)) (integral_penalty_tendsto A K hK hne (s • c))
      (Filter.Eventually.of_forall (fun N => integral_penalty_ray_antitone hPL N A K hK hconv hne hsymm c hs hst))
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hKe]

end Tusnady.LiteratureGaussian
