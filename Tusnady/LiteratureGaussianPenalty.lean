import Tusnady.ConditionedGaussianFinite
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Actual Gaussian distance penalties for Anderson's inequality

The argument takes place on the source space of an arbitrary linear map.
Thus no rank, nonsingularity, or inverse-covariance premise is needed.
The only remaining multivariate integral step is supplied by the separately
proved Prékopa--Leindler theorem; no Gaussian inequality is assumed here.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.LiteratureGaussian
open MeasureTheory Set Metric Filter
open scoped BigOperators Topology
variable {n k : ℕ}

def midpoint (x y : Fin n → ℝ) : Fin n → ℝ := (1/2:ℝ) • x+(1/2:ℝ) • y

@[simp] lemma midpoint_apply (x y : Fin n → ℝ) (i : Fin n) :
    midpoint x y i = (x i+y i)/2 := by simp [midpoint]; ring

lemma infDist_midpoint_le (K : Set (Fin n → ℝ)) (hK : IsClosed K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (x y : Fin n → ℝ) :
    infDist (midpoint x y) K ≤ (infDist x K+infDist y K)/2 := by
  obtain ⟨p,hp,hpx⟩ := hK.exists_infDist_eq_dist hne x
  obtain ⟨q,hq,hqy⟩ := hK.exists_infDist_eq_dist hne y
  have hmid : midpoint p q ∈ K := hconv hp hq (by norm_num) (by norm_num) (by norm_num)
  have hid : midpoint x y-midpoint p q = (1/2:ℝ) • (x-p)+(1/2:ℝ) • (y-q) := by
    ext i
    simp [midpoint]
    ring
  calc
    _ ≤ dist (midpoint x y) (midpoint p q) := infDist_le_dist_of_mem hmid
    _ = ‖(1/2:ℝ) • (x-p)+(1/2:ℝ) • (y-q)‖ := by rw [dist_eq_norm,hid]
    _ ≤ ‖(1/2:ℝ) • (x-p)‖+‖(1/2:ℝ) • (y-q)‖ := norm_add_le _ _
    _ = (dist x p+dist y q)/2 := by rw [norm_smul,norm_smul]; simp [dist_eq_norm]; ring
    _ = _ := by rw [hpx,hqy]

lemma infDist_neg (K : Set (Fin n → ℝ)) (hsymm : ∀ x, x ∈ K ↔ -x ∈ K)
    (x : Fin n → ℝ) : infDist (-x) K = infDist x K := by
  have hneg : (fun x : Fin n → ℝ => -x) '' K = K := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (hsymm x).1 hx
    · intro hy
      exact ⟨-y,(hsymm y).1 hy,neg_neg y⟩
  simpa only [hneg] using
    (infDist_image (x := x) (t := K) (Φ := fun z : Fin n → ℝ => -z) isometry_neg)

lemma gaussianEnergy_midpoint_le (x y : Fin k → ℝ) :
    2*gaussianEnergy k (midpoint x y) ≤ gaussianEnergy k x+gaussianEnergy k y := by
  unfold gaussianEnergy
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [midpoint_apply]
  nlinarith [sq_nonneg (x i-y i)]

lemma gaussianEnergy_neg (x : Fin k → ℝ) : gaussianEnergy k (-x) = gaussianEnergy k x := by
  simp [gaussianEnergy]

lemma continuous_standardGaussianDensity (k : ℕ) : Continuous (standardGaussianDensity k) := by
  unfold standardGaussianDensity exponentialKernel
  exact Real.continuous_exp.comp (continuous_const.sub ((continuous_gaussianEnergy k).div_const 2))

lemma standardGaussianDensity_pos (x : Fin k → ℝ) : 0 < standardGaussianDensity k x :=
  Real.exp_pos _

lemma standardGaussianDensity_neg (x : Fin k → ℝ) :
    standardGaussianDensity k (-x) = standardGaussianDensity k x := by
  unfold standardGaussianDensity exponentialKernel
  rw [gaussianEnergy_neg]

def penalty (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) (x : Fin k → ℝ) : ℝ :=
  standardGaussianDensity k x*Real.exp (-(N:ℝ)*infDist (A x-c) K)

lemma penalty_pos (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) (x : Fin k → ℝ) : 0 < penalty N A K c x :=
  mul_pos (standardGaussianDensity_pos x) (Real.exp_pos _)

lemma penalty_le_density (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) (x : Fin k → ℝ) :
    penalty N A K c x ≤ standardGaussianDensity k x := by
  apply mul_le_of_le_one_right (standardGaussianDensity_pos x).le
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg N)) infDist_nonneg

lemma penalty_continuous (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) : Continuous (penalty N A K c) := by
  apply (continuous_standardGaussianDensity k).mul
  exact Real.continuous_exp.comp
    (continuous_const.mul ((continuous_infDist_pt K).comp (A.continuous.sub continuous_const)))

lemma penalty_integrable (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) : Integrable (penalty N A K c) := by
  apply (integrable_standardGaussianDensity k).mono' (penalty_continuous N A K c).measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs,abs_of_pos (penalty_pos N A K c x)]
    exact penalty_le_density N A K c x

lemma penalty_eq_exp (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) (x : Fin k → ℝ) :
    penalty N A K c x = Real.exp (-gaussianEntropyConstant k-gaussianEnergy k x/2-
      (N:ℝ)*infDist (A x-c) K) := by
  unfold penalty standardGaussianDensity exponentialKernel
  rw [← Real.exp_add]
  congr 1
  ring

/-- Actual pointwise midpoint inequality for the three distance penalties. -/
theorem penalty_midpoint_product (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (c : Fin n → ℝ) (x y : Fin k → ℝ) :
    penalty N A K c x*penalty N A K (-c) y ≤ penalty N A K 0 (midpoint x y)^2 := by
  have hid : midpoint (A x-c) (A y-(-c)) = A (midpoint x y) := by
    ext i
    simp [midpoint]
    ring
  have hd := infDist_midpoint_le K hK hconv hne (A x-c) (A y-(-c))
  rw [hid] at hd
  have hN := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hE := gaussianEnergy_midpoint_le x y
  simp only [penalty_eq_exp,sub_zero,pow_two]
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma penalty_neg (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hsymm : ∀ x, x ∈ K ↔ -x ∈ K)
    (c : Fin n → ℝ) (x : Fin k → ℝ) : penalty N A K (-c) (-x) = penalty N A K c x := by
  have hid : A (-x)-(-c) = -(A x-c) := by rw [map_neg]; abel
  unfold penalty
  rw [standardGaussianDensity_neg,hid,infDist_neg K hsymm]

lemma integral_penalty_neg (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hsymm : ∀ x, x ∈ K ↔ -x ∈ K) (c : Fin n → ℝ) :
    (∫ x, penalty N A K (-c) x) = ∫ x, penalty N A K c x := by
  rw [← integral_neg_eq_self (penalty N A K (-c))]
  simp_rw [penalty_neg N A K hsymm c]

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureGaussian
open MeasureTheory Set Metric Filter
open scoped BigOperators Topology
variable {n k : ℕ}

/-- The common strictly positive Gaussian domination parameters are
C=exp(-gaussianEntropyConstant k) and a=1/2. -/
lemma penalty_gaussian_bound (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (c : Fin n → ℝ) (x : Fin k → ℝ) :
    penalty N A K c x ≤ Real.exp (-gaussianEntropyConstant k)*
      Real.exp (-(1/2:ℝ)*∑ i, (x i)^2) := by
  apply (penalty_le_density N A K c x).trans_eq
  unfold standardGaussianDensity exponentialKernel gaussianEnergy
  rw [← Real.exp_add]
  congr 1
  ring

/-- Actual pointwise convergence to the Gaussian density restricted to
an arbitrary closed inverse-image event. Singular A is allowed. -/
theorem penalty_tendsto (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hne : K.Nonempty)
    (c : Fin n → ℝ) (x : Fin k → ℝ) :
    Tendsto (fun N : ℕ => penalty N A K c x) atTop
      (𝓝 (({x : Fin k → ℝ | A x-c ∈ K}).indicator (standardGaussianDensity k) x)) := by
  classical
  by_cases hx : A x-c ∈ K
  · have hd : infDist (A x-c) K = 0 := infDist_zero_of_mem hx
    rw [Set.indicator_of_mem (show x ∈ {x : Fin k → ℝ | A x-c ∈ K} from hx)]
    simp only [penalty,hd,mul_zero,Real.exp_zero,mul_one]
    exact tendsto_const_nhds
  · have hd : 0 < infDist (A x-c) K := (hK.notMem_iff_infDist_pos hne).1 hx
    have hN : Tendsto (fun N : ℕ => (N:ℝ)*infDist (A x-c) K) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const' hd
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp hN
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => standardGaussianDensity k x)
      atTop (𝓝 (standardGaussianDensity k x))).mul he
    rw [Set.indicator_of_notMem (show x ∉ {x : Fin k → ℝ | A x-c ∈ K} from hx)]
    simpa only [penalty,Function.comp_apply,neg_mul,mul_zero] using ht

/-- Dominated convergence is fully discharged by the actual normalized
standard Gaussian density, independent of the penalty integer. -/
theorem integral_penalty_tendsto (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hne : K.Nonempty) (c : Fin n → ℝ) :
    Tendsto (fun N : ℕ => ∫ x, penalty N A K c x) atTop
      (𝓝 (∫ x in {x : Fin k → ℝ | A x-c ∈ K}, standardGaussianDensity k x)) := by
  have hS : MeasurableSet {x : Fin k → ℝ | A x-c ∈ K} :=
    hK.measurableSet.preimage (A.measurable.sub measurable_const)
  rw [← integral_indicator hS]
  apply tendsto_integral_of_dominated_convergence (standardGaussianDensity k)
    (fun N => (penalty_continuous N A K c).measurable.aestronglyMeasurable)
    (integrable_standardGaussianDensity k)
  · intro N
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (penalty_pos N A K c x)]
      exact penalty_le_density N A K c x
  · exact Filter.Eventually.of_forall (penalty_tendsto A K hK hne c)

end Tusnady.LiteratureGaussian

namespace Tusnady.LiteratureGaussian
open MeasureTheory Set Metric Filter
open scoped BigOperators Topology
variable {n k : ℕ}

lemma penalty_continuous_parameter (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (x : Fin k → ℝ) : Continuous (fun c => penalty N A K c x) := by
  apply continuous_const.mul
  apply Real.continuous_exp.comp
  exact continuous_const.mul ((continuous_infDist_pt K).comp (continuous_const.sub continuous_id))

theorem integral_penalty_continuous (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) : Continuous (fun c => ∫ x, penalty N A K c x) := by
  apply continuous_of_dominated (bound := standardGaussianDensity k)
  · intro c
    exact (penalty_continuous N A K c).measurable.aestronglyMeasurable
  · intro c
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (penalty_pos N A K c x)]
      exact penalty_le_density N A K c x
  · exact integrable_standardGaussianDensity k
  · exact Filter.Eventually.of_forall (penalty_continuous_parameter N A K)

theorem penalty_midpoint_product_general (N : ℕ) (A : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) (hK : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (c d : Fin n → ℝ) (x y : Fin k → ℝ) :
    penalty N A K c x*penalty N A K d y ≤ penalty N A K (midpoint c d) (midpoint x y)^2 := by
  have hid : midpoint (A x-c) (A y-d) = A (midpoint x y)-midpoint c d := by
    ext i
    simp [midpoint]
    ring
  have hd := infDist_midpoint_le K hK hconv hne (A x-c) (A y-d)
  rw [hid] at hd
  have hN := mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hE := gaussianEnergy_midpoint_le x y
  simp only [penalty_eq_exp,pow_two]
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

end Tusnady.LiteratureGaussian
