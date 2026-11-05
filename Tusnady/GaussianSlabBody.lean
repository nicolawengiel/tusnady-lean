import Tusnady.GaussianMarginals
import Tusnady.ConditionedGaussianObstruction

/-!
# Actual Gaussian discrepancy bodies

The body is the inverse image of a finite closed cube under the actual
matrix product `A B`.  Gaussian mass is obtained from hereditary
discrepancy and the proved Gaussian-cover theorem; positivity is a
conclusion.  Injectivity is used only to prove compactness.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Tusnady

/-- The actual linear discrepancy body, with threshold `t`. -/
def gaussianSlabBody {M m : ℕ}
    (C : (Fin M → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (t : ℝ) : Set (Fin M → ℝ) :=
  C ⁻¹' GaussianCover.cube m t

theorem gaussianSlabBody_isClosed {M m : ℕ}
    (C : (Fin M → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (t : ℝ) :
    IsClosed (gaussianSlabBody C t) :=
  (GaussianCover.cube_isClosed m t).preimage C.continuous_of_finiteDimensional

theorem gaussianSlabBody_convex {M m : ℕ}
    (C : (Fin M → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (t : ℝ) :
    Convex ℝ (gaussianSlabBody C t) :=
  (GaussianCover.cube_convex m t).linear_preimage C

theorem gaussianSlabBody_symmetric {M m : ℕ}
    (C : (Fin M → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (t : ℝ) (z : Fin M → ℝ) :
    z ∈ gaussianSlabBody C t ↔ -z ∈ gaussianSlabBody C t := by
  simp only [gaussianSlabBody, mem_preimage, map_neg]
  exact GaussianCover.cube_symmetric m t (C z)

theorem gaussianSlabBody_isCompact {M m : ℕ}
    (C : (Fin M → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hC : Function.Injective C) (t : ℝ) :
    IsCompact (gaussianSlabBody C t) := by
  have hcube : GaussianCover.cube m t = Icc (fun _ => -t) (fun _ => t) := by
    ext x
    simp only [GaussianCover.cube, mem_setOf_eq, mem_Icc, Pi.le_def, abs_le]
    exact forall_and
  exact (C.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hC)).isCompact_preimage
    (hcube ▸ isCompact_Icc)

/-- The fixed positive entropy rate `log(2/p₀)` in Main.pdf §7. -/
def gaussianCoverEntropyRate : ℝ :=
  -Real.log (GaussianCover.standardUnitMass.toReal / 2)

theorem gaussianCoverEntropyRate_nonneg : 0 ≤ gaussianCoverEntropyRate := by
  have hle : GaussianCover.standardUnitMass.toReal ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top (gaussianReal 0 1) _) (by simp)).mpr
      GaussianMarginals.standardUnitMass_le_one
  unfold gaussianCoverEntropyRate
  exact neg_nonneg.mpr (Real.log_nonpos (by positivity) (by linarith))

theorem gaussianCover_power_eq_exp (n : ℕ) :
    (GaussianCover.standardUnitMass / 2) ^ n =
      ENNReal.ofReal (Real.exp (-gaussianCoverEntropyRate * n)) := by
  have hp : 0 < GaussianCover.standardUnitMass.toReal / 2 :=
    div_pos GaussianMarginals.standardUnitMass_real_pos (by norm_num)
  have hfinite : GaussianCover.standardUnitMass ≠ ∞ :=
    measure_ne_top (gaussianReal 0 1) _
  rw [show -gaussianCoverEntropyRate * (n : ℝ) =
      (n : ℝ) * Real.log (GaussianCover.standardUnitMass.toReal / 2) by
    unfold gaussianCoverEntropyRate; ring]
  rw [Real.exp_nat_mul, Real.exp_log hp, ENNReal.ofReal_pow hp.le]
  congr 1
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_toReal hfinite]
  norm_num

theorem standardGaussian_matrix_variance {n M : ℕ}
    (B : Matrix (Fin n) (Fin M) ℝ) (i : Fin n) :
    Var[fun x : Fin n → ℝ => x i; (Literature.standardGaussian M).map B.mulVecLin] =
      ∑ j : Fin M, B i j ^ 2 := by
  have hmap : ((Literature.standardGaussian M).map B.mulVecLin).map (fun x => x i) =
      gaussianReal 0 (∑ j : Fin M, (⟨B i j ^ 2, sq_nonneg (B i j)⟩ : ℝ≥0)) := by
    rw [Measure.map_map (measurable_pi_apply i) B.mulVecLin.continuous_of_finiteDimensional.measurable]
    exact GaussianMarginals.standardGaussian_sum_law (B i) Finset.univ
  rw [← variance_id_map (measurable_pi_apply i).aemeasurable, hmap, variance_id_gaussianReal]
  simp

/-- The actual inverse-image body has the covering lower bound. Every
variance hypothesis is an explicit squared row norm of `B`. -/
theorem gaussianSlabBody_mass_lower {m n M : ℕ}
    (literature : Literature.Assumptions)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin M) ℝ)
    (D : ℝ) (hD : MatrixDiscrepancy.hereditary A ≤ D)
    (hB : ∀ i : Fin n, ∑ j : Fin M, B i j ^ 2 ≤ 1) :
    (GaussianCover.standardUnitMass / 2) ^ n ≤
      Literature.standardGaussian M (gaussianSlabBody (A.mulVecLin.comp B.mulVecLin) (2 * D)) := by
  have hcenter : Literature.CenteredGaussian n ((Literature.standardGaussian M).map B.mulVecLin) := by
    refine ⟨M, B, ?_⟩
    rfl
  have h := GaussianMarginals.gaussian_cover literature.sidak literature.anderson
    ((Literature.standardGaussian M).map B.mulVecLin) hcenter A D hD
    (fun i => (standardGaussian_matrix_variance B i).trans_le (hB i))
  rw [Measure.map_apply B.mulVecLin.continuous_of_finiteDimensional.measurable
    (GaussianCover.centeredEvent_isClosed A.mulVecLin D).measurableSet] at h
  exact h

/-- The size bound `n ≤ C M` gives exactly the dimension-independent
probability form required by the entropy obstruction. -/
theorem gaussianSlabBody_mass_exp_lower {m n M : ℕ}
    (literature : Literature.Assumptions)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin M) ℝ)
    (D C : ℝ) (hD : MatrixDiscrepancy.hereditary A ≤ D)
    (hB : ∀ i : Fin n, ∑ j : Fin M, B i j ^ 2 ≤ 1)
    (hsize : (n : ℝ) ≤ C * M) :
    ENNReal.ofReal (Real.exp (-(gaussianCoverEntropyRate * C) * M)) ≤
      Literature.standardGaussian M (gaussianSlabBody (A.mulVecLin.comp B.mulVecLin) (2 * D)) := by
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-gaussianCoverEntropyRate * n)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hsize gaussianCoverEntropyRate_nonneg
      nlinarith
    _ = (GaussianCover.standardUnitMass / 2) ^ n := (gaussianCover_power_eq_exp n).symm
    _ ≤ _ := gaussianSlabBody_mass_lower literature A B D hD hB

theorem gaussianSlabBody_conditioningMass_pos {m n M : ℕ}
    (literature : Literature.Assumptions)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin M) ℝ)
    (D : ℝ) (hD : MatrixDiscrepancy.hereditary A ≤ D)
    (hB : ∀ i : Fin n, ∑ j : Fin M, B i j ^ 2 ≤ 1) :
    0 < gaussianConditioningMass M (gaussianSlabBody (A.mulVecLin.comp B.mulVecLin) (2 * D)) := by
  have h := gaussianSlabBody_mass_lower literature A B D hD hB
  have hmass : 0 < Literature.standardGaussian M
      (gaussianSlabBody (A.mulVecLin.comp B.mulVecLin) (2 * D)) :=
    lt_of_lt_of_le (ENNReal.pow_pos (ENNReal.div_pos_iff.mpr
      ⟨GaussianMarginals.standardUnitMass_pos.ne', by norm_num⟩) _) h
  rw [gaussianConditioningMass_eq_gaussian_measure M
    (gaussianSlabBody_isClosed (A.mulVecLin.comp B.mulVecLin) (2 * D)).measurableSet] at hmass
  exact ENNReal.ofReal_pos.mp hmass

/-- The complete cover-to-obstruction connection. The event and its
positive Gaussian probability are constructed from `A` and `B`; they
are not additional hypotheses. The remaining assumptions describe the
actual response and error of the geometric construction. -/
theorem gaussianSlabBody_obstruction {m n M : ℕ}
    (literature : Literature.Assumptions) (hM : 0 < M)
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin M) ℝ)
    (D C : ℝ) (hD : MatrixDiscrepancy.hereditary A ≤ D)
    (hB : ∀ i : Fin n, ∑ j : Fin M, B i j ^ 2 ≤ 1)
    (hsize : (n : ℝ) ≤ C * M)
    (hAB : Function.Injective (A.mulVecLin.comp B.mulVecLin))
    (weight : Fin M → ℝ) (smin rho : ℝ) (hsmin : 0 ≤ smin) (hrho : 0 ≤ rho)
    (hweight : ∀ j, smin ≤ weight j)
    (V err : (Fin M → ℝ) → EuclideanSpace ℝ (Fin M)) (herrcont : Continuous err)
    (hresponse : ∀ u ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      V u = WithLp.toLp 2 (fun j => weight j * u j) + err u)
    (hdual : ∀ z ∈ gaussianSlabBody (A.mulVecLin.comp B.mulVecLin) (2 * D),
      ∀ u ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin M)) (V u) ≤ 2 * D)
    (herr : (∫ u, ‖err u‖ ^ 2 ∂Measure.pi (fun _ : Fin M =>
      ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1 : ℝ) 1))) ≤
      (rho * smin) ^ 2 * M) :
    (gaussianRosenblattConstant (gaussianCoverEntropyRate * C) - rho) * smin * M ≤
      2 * D := by
  exact conditionedGaussian_obstruction literature M hM
    (gaussianSlabBody_isCompact _ hAB _) (gaussianSlabBody_convex _ _)
    (gaussianSlabBody_symmetric _ _)
    (gaussianSlabBody_conditioningMass_pos literature A B D hD hB)
    (gaussianCoverEntropyRate * C)
    (gaussianSlabBody_mass_exp_lower literature A B D C hD hB hsize)
    weight smin rho (2 * D) hsmin hrho hweight V err herrcont hresponse hdual herr

end Tusnady
