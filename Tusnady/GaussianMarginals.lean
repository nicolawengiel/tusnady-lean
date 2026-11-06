import Tusnady.Rounding
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Unit-slab probabilities of centered Gaussian marginals

The marginal comparison in Main.pdf Lemma 7.1 is proved from mathlib's
actual Gaussian scaling and addition laws. No free slab-mass hypothesis
is added to the literature assumptions.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
namespace Tusnady.GaussianMarginals

theorem standardUnitMass_pos : 0 < GaussianCover.standardUnitMass := by
  have hvol : volume {x : ℝ | |x| ≤ 1} ≠ 0 := by
    have hset : {x : ℝ | |x| ≤ 1} = Set.Icc (-1 : ℝ) 1 := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]
    rw [hset, Real.volume_Icc]
    norm_num
  apply pos_iff_ne_zero.mpr
  intro hzero
  exact hvol (gaussianReal_absolutelyContinuous' (0 : ℝ) (by norm_num : (1 : ℝ≥0) ≠ 0) hzero)

theorem standardUnitMass_le_one : GaussianCover.standardUnitMass ≤ 1 :=
  prob_le_one

theorem standardUnitMass_real_pos : 0 < GaussianCover.standardUnitMass.toReal := by
  exact ENNReal.toReal_pos standardUnitMass_pos.ne'
    (measure_ne_top (gaussianReal 0 1) _)

/-- A centered real Gaussian of variance at most one puts at least the
standard Gaussian unit-interval mass into `[-1,1]`, including variance zero. -/
theorem gaussianReal_unit_mass_lower (v : ℝ≥0) (hv : v ≤ 1) :
    GaussianCover.standardUnitMass ≤ gaussianReal 0 v {x : ℝ | |x| ≤ 1} := by
  let c : ℝ := (NNReal.sqrt v : ℝ)
  have hc0 : 0 ≤ c := NNReal.coe_nonneg _
  have hc1 : c ≤ 1 := by exact_mod_cast (NNReal.sqrt_le_one.mpr hv)
  have hvar : (⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) = v := by
    apply NNReal.coe_injective
    exact_mod_cast NNReal.sq_sqrt v
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => c * x) = gaussianReal 0 v := by
    simpa [NNReal.mk, hvar] using (gaussianReal_map_const_mul (μ := 0) (v := 1) c)
  rw [← hmap, Measure.map_apply (by fun_prop) (isClosed_le continuous_abs continuous_const).measurableSet]
  apply measure_mono
  intro x hx
  change |c * x| ≤ 1
  rw [abs_mul, abs_of_nonneg hc0]
  exact (mul_le_mul_of_nonneg_left hx hc0).trans (by simpa using hc1)

/-- Every finite linear combination of the independent standard Gaussian
coordinates has its actual Gaussian law, including zero coefficients. -/
theorem standardGaussian_sum_law {k : ℕ} (a : Fin k → ℝ) (S : Finset (Fin k)) :
    (Literature.standardGaussian k).map (fun z => ∑ j ∈ S, a j * z j) =
      gaussianReal 0 (∑ j ∈ S, (⟨a j ^ 2, sq_nonneg (a j)⟩ : ℝ≥0)) := by
  classical
  let P := Literature.standardGaussian k
  letI : IsProbabilityMeasure P := by
    dsimp [P, Literature.standardGaussian]
    infer_instance
  have hmeas : ∀ j : Fin k, Measurable (fun z : Fin k → ℝ => a j * z j) := by
    intro j
    fun_prop
  have hind : iIndepFun (fun j : Fin k => fun z : Fin k → ℝ => a j * z j) P := by
    exact iIndepFun_pi (fun j => (measurable_const.mul measurable_id).aemeasurable)
  have hcoord : ∀ j : Fin k, P.map (fun z => a j * z j) =
      gaussianReal 0 (⟨a j ^ 2, sq_nonneg (a j)⟩ : ℝ≥0) := by
    intro j
    have heval : P.map (fun z : Fin k → ℝ => z j) = gaussianReal 0 1 := by
      exact (measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) j).map_eq
    calc
      P.map (fun z => a j * z j) =
          (P.map (fun z : Fin k → ℝ => z j)).map (fun x => a j * x) :=
        (Measure.map_map (by fun_prop) (by fun_prop)).symm
      _ = gaussianReal 0 (⟨a j ^ 2, sq_nonneg (a j)⟩ : ℝ≥0) := by
        rw [heval, gaussianReal_map_const_mul]
        simp [NNReal.mk]
  induction S using Finset.induction_on with
  | empty => simp [gaussianReal_zero_var]
  | @insert j S hj ih =>
    have hpair := (hind.indepFun_finsetSum_of_notMem hmeas hj).symm
    have hfun : (∑ l ∈ S, fun z : Fin k → ℝ => a l * z l) =
        (fun z : Fin k → ℝ => ∑ l ∈ S, a l * z l) := by
      funext z
      simp only [Finset.sum_apply]
    have hsum : P.map (∑ l ∈ S, fun z : Fin k → ℝ => a l * z l) =
        gaussianReal 0 (∑ l ∈ S, (⟨a l ^ 2, sq_nonneg (a l)⟩ : ℝ≥0)) := by
      simpa only [hfun] using ih
    have h := gaussianReal_add_gaussianReal_of_indepFun hpair
      ⟨(hmeas j).aemeasurable, hcoord j⟩
      ⟨by
        rw [hfun]
        exact (Finset.measurable_sum S (fun l _ => hmeas l)).aemeasurable, hsum⟩
    have hadd : ((fun z : Fin k → ℝ => a j * z j) +
        ∑ l ∈ S, fun z : Fin k → ℝ => a l * z l) =
        (fun z => ∑ l ∈ insert j S, a l * z l) := by
      funext z
      simp only [Pi.add_apply, Finset.sum_apply, Finset.sum_insert hj]
    rw [hadd] at h
    simpa only [Finset.sum_insert hj, zero_add] using h

/-- Each coordinate of the matrix-defined centered Gaussian measure has
an actual centered real Gaussian law. This is proved from independent
Gaussian sums, not added as another Gaussian axiom. -/
theorem centeredGaussian_coordinate_law {n : ℕ}
    (μ : Measure (Fin n → ℝ)) (hGaussian : Literature.CenteredGaussian n μ)
    (i : Fin n) : ∃ v : ℝ≥0, μ.map (fun x => x i) = gaussianReal 0 v := by
  rcases hGaussian with ⟨k, B, rfl⟩
  refine ⟨∑ j : Fin k, (⟨B i j ^ 2, sq_nonneg (B i j)⟩ : ℝ≥0), ?_⟩
  have hB : Measurable (fun z : Fin k → ℝ => fun l : Fin n => ∑ j, B l j * z j) := by
    apply measurable_pi_lambda
    intro l
    fun_prop
  rw [Measure.map_map (measurable_pi_apply i) hB]
  exact standardGaussian_sum_law (B i) Finset.univ

/-- A variance bound on a true centered-Gaussian coordinate implies the
specific fixed slab-mass bound used by the cover argument. -/
theorem centeredGaussian_unit_marginal_lower {n : ℕ}
    (μ : Measure (Fin n → ℝ)) (hGaussian : Literature.CenteredGaussian n μ)
    (i : Fin n) (hvariance : Var[fun x : Fin n → ℝ => x i; μ] ≤ 1) :
    GaussianCover.standardUnitMass ≤ μ {x | |x i| ≤ 1} := by
  obtain ⟨v, hlaw⟩ := centeredGaussian_coordinate_law μ hGaussian i
  have hvvar : (v : ℝ) = Var[fun x : Fin n → ℝ => x i; μ] := by
    calc
      (v : ℝ) = Var[id; gaussianReal 0 v] := variance_id_gaussianReal.symm
      _ = Var[id; μ.map (fun x => x i)] := by rw [hlaw]
      _ = Var[fun x : Fin n → ℝ => x i; μ] :=
        variance_id_map (measurable_pi_apply i).aemeasurable
  have hv : v ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_one, hvvar] using hvariance
  calc
    GaussianCover.standardUnitMass ≤ gaussianReal 0 v {x : ℝ | |x| ≤ 1} :=
      gaussianReal_unit_mass_lower v hv
    _ = μ {x | |x i| ≤ 1} := by
      rw [← hlaw, Measure.map_apply (measurable_pi_apply i)
        (isClosed_le continuous_abs continuous_const).measurableSet]
      rfl

/-- Main.pdf Lemma 7.1 in full: actual hereditary matrix discrepancy,
actual coordinate variance bounds and the named Sidak/Anderson literature
inputs imply the Gaussian small-ball bound. Rounding, marginal comparison,
linear-image Gaussianity and finite covering are all proved in the chain.
No free rounding-cover or marginal-mass hypothesis remains. -/
theorem gaussian_cover {m n : ℕ}
    (hSidak : Literature.Sidak) (hAnderson : Literature.Anderson)
    (μ : Measure (Fin n → ℝ))
    (hGaussian : Literature.CenteredGaussian n μ)
    (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hD : MatrixDiscrepancy.hereditary A ≤ D)
    (hvariance : ∀ i : Fin n, Var[fun x : Fin n → ℝ => x i; μ] ≤ 1) :
    (GaussianCover.standardUnitMass / 2) ^ n ≤
      μ (GaussianCover.centeredEvent A.mulVecLin D) :=
  Rounding.gaussian_cover_of_marginals hSidak hAnderson μ hGaussian A D hD
    (fun i => centeredGaussian_unit_marginal_lower μ hGaussian i (hvariance i))

end Tusnady.GaussianMarginals
