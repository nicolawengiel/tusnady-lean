import Tusnady.Upper.PrefixGaussian
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Proved low-dimensional cases of the concrete Gaussian fold

This file establishes genuine special cases of the analytic dependency in
`PrefixGaussian.lean`.  It does not discharge `GaussianFoldMonotonicity`, whose
quantifier still ranges over every dimension.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory

namespace Tusnady.Upper

/-- In every dimension the zero-vector transform is the identity. -/
theorem gaussianFold_mass_zero (k : ℕ) (K : Set (EuclideanSpace ℝ (Fin k))) :
    (euclideanGaussian k).real K ≤ (euclideanGaussian k).real (signingFold 0 K) := by
  rw [signingFold_zero]

/-- Dimension zero, with no convexity or mass premise needed. -/
theorem gaussianFold_mass_dimension_zero (K : Set (EuclideanSpace ℝ (Fin 0)))
    (u : EuclideanSpace ℝ (Fin 0)) :
    (euclideanGaussian 0).real K ≤ (euclideanGaussian 0).real (signingFold u K) := by
  have hu : u = 0 := by
    ext i
    exact Fin.elim0 i
  subst u
  exact gaussianFold_mass_zero 0 K

/-- The scalar fold is unchanged when its direction is negated. -/
theorem signingFold_neg_direction_real (K : Set ℝ) (u : ℝ) :
    signingFold (-u) K = signingFold u K := by
  have h : ∀ v : ℝ, signingFold (-v) K ⊆ signingFold v K := by
    intro v x hx
    obtain ⟨c, t, hm, hp, ht, heq⟩ := (mem_signingFold_iff K (-v) x).1 hx
    apply (mem_signingFold_iff K v x).2
    refine ⟨c, -t, ?_, ?_, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    · simpa only [sub_eq_add_neg] using hp
    · simpa using hm
    · simpa using heq
  exact Set.Subset.antisymm (h u) (by simpa using h (-u))

/-- An interval symmetric about zero contains its own fold whenever it contains
the step.  This is the special geometric fact specific to one dimension. -/
theorem subset_signingFold_real (K : Set ℝ) (hconv : Convex ℝ K)
    (hsymm : ∀ x ∈ K, -x ∈ K) (u : ℝ) (hu : u ∈ K) : K ⊆ signingFold u K := by
  have hpos : ∀ v : ℝ, 0 < v → v ∈ K → K ⊆ signingFold v K := by
    intro v hv hvK x hx
    have hmK := hsymm v hvK
    have hzK : (0 : ℝ) ∈ K := hconv.ordConnected.out hmK hvK ⟨by linarith, hv.le⟩
    by_cases hxp : v ≤ x
    · apply (mem_signingFold_iff K v x).2
      refine ⟨x - v, 1, ?_, by simpa, by norm_num, by simp⟩
      exact hconv.ordConnected.out (hsymm x hx) hx ⟨by linarith, by linarith⟩
    · by_cases hxm : x ≤ -v
      · apply (mem_signingFold_iff K v x).2
        refine ⟨x + v, -1, by simpa, ?_, by norm_num, by simp⟩
        exact hconv.ordConnected.out hx (hsymm x hx) ⟨by linarith, by linarith⟩
      · apply (mem_signingFold_iff K v x).2
        refine ⟨0, x / v, by simpa using hmK, by simpa using hvK, ?_, ?_⟩
        · constructor
          · apply (le_div_iff₀ hv).2
            linarith
          · apply (div_le_iff₀ hv).2
            linarith
        · simp [smul_eq_mul, hv.ne']
  rcases lt_trichotomy 0 u with hp | hz | hn
  · exact hpos u hp hu
  · rw [← hz, signingFold_zero]
  · rw [← signingFold_neg_direction_real K u]
    exact hpos (-u) (by linarith) (hsymm u hu)

/-- A deliberately coarse bound, sufficient for the radius `1/5` argument. -/
theorem standardGaussianPDFReal_le_one (x : ℝ) : gaussianPDFReal 0 1 x ≤ 1 := by
  have hs : 1 ≤ Real.sqrt (2 * Real.pi) := Real.one_le_sqrt.mpr (by linarith [Real.two_le_pi])
  have hi : (Real.sqrt (2 * Real.pi))⁻¹ ≤ 1 := inv_le_one₀ (by positivity) |>.2 hs
  have he : Real.exp (-x^2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  simpa only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero] using
    mul_le_mul hi he (Real.exp_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

/-- The standard Gaussian puts strictly less than half its mass in the tiny
central interval needed here.  This is proved from its actual density. -/
theorem standardGaussian_small_interval_mass :
    (gaussianReal 0 1).real (Icc (-(1 / 5 : ℝ)) (1 / 5)) ≤ (2 / 5 : ℝ) := by
  have hi : (gaussianReal 0 1).real (Icc (-(1 / 5 : ℝ)) (1 / 5)) =
      ∫ x in Icc (-(1 / 5 : ℝ)) (1 / 5), gaussianPDFReal 0 1 x := by
    rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num)]
    exact ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))
  rw [hi]
  calc
    (∫ x in Icc (-(1 / 5 : ℝ)) (1 / 5), gaussianPDFReal 0 1 x) ≤
        ∫ _ in Icc (-(1 / 5 : ℝ)) (1 / 5), (1 : ℝ) := by
      exact setIntegral_mono_on (integrable_gaussianPDFReal 0 1).integrableOn
        (integrableOn_const measure_Icc_lt_top.ne) measurableSet_Icc
        (fun x _ => standardGaussianPDFReal_le_one x)
    _ = (2 / 5 : ℝ) := by
      rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def, Real.volume_Icc]
      norm_num

/-- A symmetric convex real set of Gaussian mass at least half contains every
step of absolute value at most `1/5`. -/
theorem mem_of_convex_symmetric_gaussian_mass_real (K : Set ℝ)
    (hconv : Convex ℝ K) (hsymm : ∀ x ∈ K, -x ∈ K)
    (hmass : (1 : ℝ) / 2 ≤ (gaussianReal 0 1).real K)
    (u : ℝ) (hu : |u| ≤ (1 : ℝ) / 5) : u ∈ K := by
  by_contra hnot
  have hsub : K ⊆ Icc (-(1 / 5 : ℝ)) (1 / 5) := by
    intro x hx
    by_contra hxnot
    have hux := abs_le.mp hu
    have habs : (1 : ℝ) / 5 < |x| := by
      by_contra h
      exact hxnot (abs_le.mp (not_lt.mp h))
    have huK : u ∈ K := by
      rcases le_total 0 x with hp | hn
      · rw [abs_of_nonneg hp] at habs
        exact hconv.ordConnected.out (hsymm x hx) hx ⟨by linarith [hux.1], by linarith [hux.2]⟩
      · rw [abs_of_nonpos hn] at habs
        exact hconv.ordConnected.out hx (hsymm x hx) ⟨by linarith [hux.1], by linarith [hux.2]⟩
    exact hnot huK
  have hm := (measureReal_mono hsub).trans standardGaussian_small_interval_mass
  linarith

/-- Genuine one-dimensional analytic monotonicity, with no literature input. -/
theorem gaussianReal_signingFold_mass (K : Set ℝ) (hconv : Convex ℝ K)
    (hsymm : ∀ x ∈ K, -x ∈ K) (hmass : (1 : ℝ) / 2 ≤ (gaussianReal 0 1).real K)
    (u : ℝ) (hu : |u| ≤ (1 : ℝ) / 5) :
    (gaussianReal 0 1).real K ≤ (gaussianReal 0 1).real (signingFold u K) := by
  exact measureReal_mono (subset_signingFold_real K hconv hsymm u
    (mem_of_convex_symmetric_gaussian_mass_real K hconv hsymm hmass u hu))

private def oneVector (x : ℝ) : EuclideanSpace ℝ (Fin 1) :=
  WithLp.toLp 2 (fun _ => x)

private def oneVectorLinear : ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toFun := oneVector
  map_add' := by intro x y; ext i; simp [oneVector]
  map_smul' := by intro r x; ext i; simp [oneVector]

private theorem oneVector_coordinate (z : EuclideanSpace ℝ (Fin 1)) :
    oneVector (z 0) = z := by
  ext i
  fin_cases i
  rfl

private theorem continuous_oneVector : Continuous oneVector :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp (continuous_pi fun _ => continuous_id)

/-- The coordinate has the actual scalar Gaussian law under our transported
product Gaussian; no alternative Gaussian measure is introduced. -/
theorem euclideanGaussian_coordinate_one_law :
    (euclideanGaussian 1).map (fun z : EuclideanSpace ℝ (Fin 1) => z 0) =
      gaussianReal 0 1 := by
  rw [euclideanGaussian, Measure.map_map (by fun_prop)
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable]
  simpa only [Literature.standardGaussian, Function.comp_def, PiLp.toLp_apply] using
    (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq

/-- Dimension one in the exact Euclidean space and Gaussian convention of the
open all-dimensional statement.  All analytical hypotheses are proved here. -/
theorem gaussianFold_mass_dimension_one (K : Set (EuclideanSpace ℝ (Fin 1)))
    (hKcomp : IsCompact K) (hKconv : Convex ℝ K) (hKsymm : ∀ x ∈ K, -x ∈ K)
    (hmass : (1 : ℝ) / 2 ≤ (euclideanGaussian 1).real K)
    (u : EuclideanSpace ℝ (Fin 1)) (hu : ‖u‖ ≤ (1 : ℝ) / 5) :
    (euclideanGaussian 1).real K ≤ (euclideanGaussian 1).real (signingFold u K) := by
  let S : Set ℝ := oneVector ⁻¹' K
  have hSconv : Convex ℝ S := hKconv.linear_preimage oneVectorLinear
  have hSsymm : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    have h := hKsymm (oneVector x) hx
    change oneVector (-x) ∈ K
    have heq : oneVector (-x) = -oneVector x := oneVectorLinear.map_neg x
    exact heq ▸ h
  have hSmeas : MeasurableSet S := (hKcomp.isClosed.preimage continuous_oneVector).measurableSet
  have hmass_eq : (euclideanGaussian 1).real K = (gaussianReal 0 1).real S := by
    rw [← euclideanGaussian_coordinate_one_law, measureReal_def, measureReal_def,
      Measure.map_apply (by fun_prop) hSmeas]
    congr 2
    ext z
    simp only [mem_preimage, S, oneVector_coordinate]
  have hSmass : (1 : ℝ) / 2 ≤ (gaussianReal 0 1).real S := hmass_eq ▸ hmass
  have hcoordinate : |u 0| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u 0
  have hcoord : |u 0| ≤ (1 : ℝ) / 5 := hcoordinate.trans hu
  have huS := mem_of_convex_symmetric_gaussian_mass_real S hSconv hSsymm hSmass (u 0) hcoord
  refine measureReal_mono (μ := euclideanGaussian 1) ?_
  intro x hx
  have hxS : x 0 ∈ S := by simpa only [S, mem_preimage, oneVector_coordinate] using hx
  have hxFold := subset_signingFold_real S hSconv hSsymm (u 0) huS hxS
  obtain ⟨c, t, hm, hp, ht, heq⟩ := (mem_signingFold_iff S (u 0) (x 0)).1 hxFold
  apply (mem_signingFold_iff K u x).2
  refine ⟨oneVector c, t, ?_, ?_, ht, ?_⟩
  · have he : oneVector (c - u 0) = oneVector c - u := by
      rw [show oneVector (c - u 0) = oneVector c - oneVector (u 0) from
        oneVectorLinear.map_sub c (u 0), oneVector_coordinate]
    exact he ▸ hm
  · have he : oneVector (c + u 0) = oneVector c + u := by
      rw [show oneVector (c + u 0) = oneVector c + oneVector (u 0) from
        oneVectorLinear.map_add c (u 0), oneVector_coordinate]
    exact he ▸ hp
  · ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simpa only [PiLp.add_apply, PiLp.smul_apply, oneVector, PiLp.toLp_apply] using heq

end Tusnady.Upper
