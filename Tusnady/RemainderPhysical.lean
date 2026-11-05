import Tusnady.RemainderDensity
import Tusnady.PrimitiveEvaluation
import Tusnady.ShellHighProjection

/-! # Physical remainder identities, including every sampled point

Pointwise primitive evaluation is an actual integral-kernel continuous
linear map. Scalar Parseval therefore proves the energy-density identity
at every point of the unit cube, not just almost everywhere in space.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.Witness

def linearTestL2 (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) : CubeHilbert d :=
  ∑ R : Shell d h, (linearCoefficient j theta R * u R) • qShellVector R

theorem linearTestL2_ae (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) :
    linearTestL2 j theta u =ᵐ[Haar.cubeMeasure d] linearTestFunction j theta u := by
  apply Haar.finite_sum_ae Finset.univ
    (fun R : Shell d h => (linearCoefficient j theta R * u R) • qShellVector R)
    (fun R p => linearCoefficient j theta R * u R * qShell R p)
  intro R _
  filter_upwards [Lp.coeFn_smul (linearCoefficient j theta R * u R) (qShellVector R),
    qShellVector_ae R] with p hs hq
  simp only [hs, hq, Pi.smul_apply, smul_eq_mul]

theorem cubicTestL2_eq_sub (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) :
    cubicTestL2 j theta u = testL2 j theta u - linearTestL2 j theta u := by
  apply Lp.ext
  filter_upwards [cubicTestL2_ae j theta u, testL2_ae j theta u, linearTestL2_ae j theta u,
    Lp.coeFn_sub (testL2 j theta u) (linearTestL2 j theta u)] with p hc ht hl hs
  rw [hc, hs, Pi.sub_apply, ht, hl]

theorem pointPrimitiveHighCLM_qShellVector (hd : 0 < d) (R : Shell d h)
    (p : Point d) (hp : p ∈ UnitCube d) :
    Haar.pointPrimitiveHighCLM d (h+3*d) h p (qShellVector R) =
      shellVolume h * normalizedPrimitive R p := by
  change Haar.pointPrimitiveCLM d p (Haar.highProjection d (h+3*d) h (qShellVector R)) = _
  rw [highProjection_qShellVector hd R, Haar.pointPrimitiveCLM_eq_boxPrimitive d p hp,
    Haar.boxPrimitive_congr_cube_ae _ _ (qShellVector_ae R) p hp,
    boxPrimitive_qShell_normalized R p hp]

theorem pointPrimitiveHighCLM_linearTestL2 (hd : 0 < d) (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (p : Point d) (hp : p ∈ UnitCube d) :
    Haar.pointPrimitiveHighCLM d (h+3*d) h p (linearTestL2 j theta u) =
      linearPrimitiveValue j theta u p := by
  simp only [linearTestL2, map_sum, map_smul, smul_eq_mul,
    pointPrimitiveHighCLM_qShellVector hd _ p hp, linearPrimitiveValue, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  ring

def physicalRemainder (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) (p : Point d) : ℝ :=
  boxPrimitive (Haar.highProjection d (h+3*d) h (testL2 j theta u)) p -
    linearPrimitiveValue j theta u p

/-- Exact physical identity `JΦ(W-Wlin)=JΦW-Flin` at every cube point. -/
theorem pointPrimitiveHighCLM_cubic_eq_physical (hd : 0 < d) (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (p : Point d) (hp : p ∈ UnitCube d) :
    Haar.pointPrimitiveHighCLM d (h+3*d) h p (cubicTestL2 j theta u) =
      physicalRemainder j theta u p := by
  rw [cubicTestL2_eq_sub, map_sub, pointPrimitiveHighCLM_linearTestL2 hd j theta u p hp,
    Haar.pointPrimitiveHighCLM_eq_boxPrimitive d (h+3*d) h p hp]
  rfl

theorem cubic_norm_sq_eq_integral_physical (hd : 0 < d) (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) :
    ‖Haar.primitiveHighCLM d (h+3*d) h (cubicTestL2 j theta u)‖ ^ 2 =
      ∫ p, physicalRemainder j theta u p ^ 2 ∂Haar.cubeMeasure d := by
  rw [Haar.primitiveHighCLM_norm_sq]
  apply integral_congr_ae
  filter_upwards [Haar.cubeMeasure_ae_UnitCube d] with p hp
  have hpoint := pointPrimitiveHighCLM_cubic_eq_physical hd j theta u p hp
  rw [Haar.pointPrimitiveHighCLM_eq_boxPrimitive d (h+3*d) h p hp] at hpoint
  rw [hpoint]

/-- The energy identity holds at every point, hence at all sampled
points, with no spatial exceptional set to avoid. -/
theorem cubicEnergyDensity_eq_point_expectation (j : Fin d) (theta : ℝ)
    (p : Point d) (hp : p ∈ UnitCube d) :
    cubicEnergyDensity (h := h) j theta p =
      ∫ u, boxPrimitive (Haar.highProjection d (h+3*d) h (cubicTestL2 j theta u)) p ^ 2
        ∂UniformMonomial.cubeLaw (Shell d h) := by
  have heq := expected_cubic_operator_sq (h := h) j theta (Haar.pointPrimitiveHighCLM d (h+3*d) h p)
  simp_rw [Haar.pointPrimitiveHighCLM_eq_boxPrimitive d (h+3*d) h p hp,
    Real.norm_eq_abs, sq_abs] at heq
  exact heq.symm

theorem cubicEnergyDensity_eq_physical_expectation (hd : 0 < d) (j : Fin d) (theta : ℝ)
    (p : Point d) (hp : p ∈ UnitCube d) :
    cubicEnergyDensity (h := h) j theta p =
      ∫ u, physicalRemainder j theta u p ^ 2 ∂UniformMonomial.cubeLaw (Shell d h) := by
  rw [cubicEnergyDensity_eq_point_expectation j theta p hp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    have heq := pointPrimitiveHighCLM_cubic_eq_physical hd j theta u p hp
    rw [Haar.pointPrimitiveHighCLM_eq_boxPrimitive d (h+3*d) h p hp] at heq
    exact congrArg (fun x : ℝ => x ^ 2) heq

theorem continuous_cubicTestL2 (j : Fin d) (theta : ℝ) :
    Continuous (cubicTestL2 (h := h) j theta) := by
  apply continuous_finset_sum
  intro G _
  exact (continuous_const.mul (cellMonomial_continuous G.1 G.2)).smul continuous_const

theorem cubic_operator_sq_integrable (j : Fin d) (theta : ℝ)
    (O : CubeHilbert d →L[ℝ] ℝ) :
    Integrable (fun u => O (cubicTestL2 (h := h) j theta u) ^ 2)
      (UniformMonomial.cubeLaw (Shell d h)) := by
  have hcont := O.continuous.comp (continuous_cubicTestL2 (h := h) j theta)
  obtain ⟨B, hB⟩ := (isCompact_Icc.image hcont).isBounded.exists_norm_le
  have hLp : MemLp (fun u => O (cubicTestL2 (h := h) j theta u)) 2
      (UniformMonomial.cubeLaw (Shell d h)) := by
    apply MemLp.of_bound hcont.measurable.aestronglyMeasurable B
    filter_upwards [UniformMonomial.ae_cube (Shell d h)] with u hu
    apply hB
    refine ⟨u, ?_, rfl⟩
    exact ⟨fun i => (abs_le.mp (hu i)).1, fun i => (abs_le.mp (hu i)).2⟩
  exact hLp.integrable_sq

theorem physical_remainder_sq_integrable (hd : 0 < d) (j : Fin d) (theta : ℝ)
    (p : Point d) (hp : p ∈ UnitCube d) :
    Integrable (fun u => physicalRemainder j theta u p ^ 2)
      (UniformMonomial.cubeLaw (Shell d h)) := by
  have hi := cubic_operator_sq_integrable (h := h) j theta (Haar.pointPrimitiveHighCLM d (h+3*d) h p)
  exact hi.congr (Filter.Eventually.of_forall fun u =>
    congrArg (fun x : ℝ => x ^ 2) (pointPrimitiveHighCLM_cubic_eq_physical hd j theta u p hp))

/-- Actual weighted mean-square sampled remainder: the same deterministic
point list and weights are used on both sides. -/
theorem expected_weighted_physical_remainder (hd : 0 < d) (j : Fin d) (theta : ℝ)
    {n : ℕ} (a : Fin n → ℝ) (P : Fin n → Point d) (hP : ∀ i, P i ∈ UnitCube d) :
    (∫ u, ∑ i : Fin n, a i * physicalRemainder j theta u (P i) ^ 2
      ∂UniformMonomial.cubeLaw (Shell d h)) =
      ∑ i : Fin n, a i * cubicEnergyDensity (h := h) j theta (P i) := by
  rw [integral_finset_sum Finset.univ (fun i _ =>
    (physical_remainder_sq_integrable hd j theta (P i) (hP i)).const_mul (a i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, ← cubicEnergyDensity_eq_physical_expectation hd j theta (P i) (hP i)]

end Tusnady.Witness
