import Tusnady.Upper.Ehrhard.Minkowski
import Tusnady.Upper.Ehrhard.GaussianBallAsymptotics
import Tusnady.Upper.Ehrhard.ClosedBallApproximation
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.Analysis.Normed.Group.Pointwise
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Gaussian isoperimetry for compact convex sets containing the origin

This is derived from the proved compact Ehrhard inequality and the proved
asymptotic unit quantile slope of Gaussian balls. Enlarging the endpoint body
before taking its small mixture avoids any assumed continuity of dilations.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal InnerProductSpace Pointwise Topology
namespace OAI.GaussianPropeller
open Quantile ConvexLift

lemma compact_gaussian_mass_lt_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (A : Set (EuclideanSpace ℝ ι)) (hAc : IsCompact A) :
    (gaussianMeasure ι).real A < 1 := by
  obtain ⟨R, hR⟩ := hAc.isBounded.exists_norm_le
  have hsub : A ⊆ Metric.closedBall (0 : EuclideanSpace ℝ ι) R := by
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR x hx
  exact (measureReal_mono hsub).trans_lt (gaussian_ball_mass_lt_one R)

/-- Convex Gaussian isoperimetry with the actual Minkowski parallel body. -/
theorem compactConvex_gaussian_isoperimetry {k : ℕ} (hk : 0 < k)
    (K : Set (EuclideanSpace ℝ (Fin k))) (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKzero : (0 : EuclideanSpace ℝ (Fin k)) ∈ K)
    (hKm : (gaussianMeasure (Fin k)).real K ∈ Ioo (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) :
    Φ (q ((gaussianMeasure (Fin k)).real K)+r) ≤
      (gaussianMeasure (Fin k)).real (K + Metric.closedBall 0 r) := by
  letI : NeZero k := ⟨hk.ne'⟩
  rcases hr.eq_or_lt with rfl | hr
  · simp [Φ_q hKm]
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ)+2)
  let R : ℕ → ℝ := fun n => r*((n : ℝ)+2)
  have ht (n : ℕ) : t n ∈ Ioo (0:ℝ) 1 := by
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [t]
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith)
  have htlim : Tendsto t atTop (𝓝 (0:ℝ)) := by
    have h := (tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hRlim : Tendsto R atTop atTop := by
    apply Tendsto.const_mul_atTop hr
    simpa only [add_comm] using tendsto_atTop_add_const_left atTop 2
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have htR (n : ℕ) : t n * R n = r := by
    have hn : (n : ℝ)+2 ≠ 0 := by positivity
    dsimp [t, R]
    field_simp
  have hqtlim : Tendsto
      (fun n => t n * q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (R n))))
      atTop (𝓝 r) := by
    have h := (gaussian_ball_quantile_div_tendsto_one (ι := Fin k)).comp hRlim
    have heq (n : ℕ) : t n * q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (R n))) =
        r * (q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (R n))) / R n) := by
      have hn : (n : ℝ)+2 ≠ 0 := by positivity
      dsimp [t, R]
      field_simp
    simpa only [Function.comp_def, ← heq, mul_one] using h.const_mul r
  have hlim : Tendsto
      (fun n => Φ ((1-t n)*q ((gaussianMeasure (Fin k)).real K) +
        t n*q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (R n)))))
      atTop (𝓝 (Φ (q ((gaussianMeasure (Fin k)).real K)+r))) := by
    have h := (((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).mul_const
      (q ((gaussianMeasure (Fin k)).real K))).add hqtlim
    simpa only [Function.comp_def, sub_zero, one_mul] using continuous_Φ.continuousAt.tendsto.comp h
  apply le_of_tendsto hlim
  have hbpos := (gaussian_ball_mass_eventually_ge_cdf (ι := Fin k)
    (a := 0) le_rfl (by norm_num)).filter_mono hRlim
  filter_upwards [hbpos] with n hBn
  let A : Set (EuclideanSpace ℝ (Fin k)) := (1-t n)⁻¹ • K
  let B : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall 0 (R n)
  have htp : 0 < 1-t n := by linarith [(ht n).2]
  have hAcomp : IsCompact A := hKc.smul _
  have hAv : Convex ℝ A := hKv.smul _
  have hKA : K ⊆ A := by
    intro x hx
    apply hKv.mem_smul_of_zero_mem hKzero hx
    exact (one_le_inv₀ htp).mpr (by linarith [(ht n).1])
  have hAm : (gaussianMeasure (Fin k)).real A ∈ Ioo (0:ℝ) 1 :=
    ⟨hKm.1.trans_le (measureReal_mono hKA), compact_gaussian_mass_lt_one A hAcomp⟩
  have hBm : (gaussianMeasure (Fin k)).real B ∈ Ioo (0:ℝ) 1 :=
    ⟨(Φ_pos (0*R n)).trans_le hBn, gaussian_ball_mass_lt_one (R n)⟩
  have heq : mixture A B (1-t n) (t n) = K + Metric.closedBall 0 r := by
    rw [mixture_eq_smul_add]
    dsimp only [A, B]
    rw [smul_smul, mul_inv_cancel₀ htp.ne', one_smul,
      smul_closedBall' (ht n).1.ne' (0 : EuclideanSpace ℝ (Fin k)) (R n)]
    simp only [smul_zero, Real.norm_eq_abs, abs_of_pos (ht n).1, htR]
  have hmix := compactConvex_gaussian_cdf_mixture A B hAcomp (isCompact_closedBall 0 _)
    hAv (convex_closedBall 0 _) hAm hBm htp.le (ht n).1.le (by ring)
  rw [heq] at hmix
  apply le_trans _ hmix
  apply strictMono_Φ.monotone
  have hq := strictMonoOn_q.monotoneOn hKm hAm (measureReal_mono hKA)
  have hmul := mul_le_mul_of_nonneg_left hq htp.le
  dsimp only [B]
  linarith only [hmul]

/-- Gaussian isoperimetry for every closed convex set containing the origin.
Compactness is removed by an actual increasing ball exhaustion and probability
convergence, while the enlarged-body probability is bounded by inclusion. -/
theorem closedConvex_gaussian_isoperimetry {k : ℕ} (hk : 0 < k)
    (K : Set (EuclideanSpace ℝ (Fin k))) (hKc : IsClosed K) (hKv : Convex ℝ K)
    (hKzero : (0 : EuclideanSpace ℝ (Fin k)) ∈ K)
    (hKm : (gaussianMeasure (Fin k)).real K ∈ Ioo (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) :
    Φ (q ((gaussianMeasure (Fin k)).real K)+r) ≤
      (gaussianMeasure (Fin k)).real (K + Metric.closedBall 0 r) := by
  open ClosedBallApproximation in
  have hmlim := measure_ballApprox_tendsto (gaussianMeasure (Fin k)) K hKc
  have hqlim := (continuousAt_q hKm).tendsto.comp hmlim
  have hlim := continuous_Φ.continuousAt.tendsto.comp (hqlim.add_const r)
  apply le_of_tendsto hlim
  filter_upwards [eventually_measure_ballApprox_mem_Ioo (gaussianMeasure (Fin k)) K hKc hKm]
    with n hmn
  exact (compactConvex_gaussian_isoperimetry hk (ballApprox K n)
    (isCompact_ballApprox K hKc n) (convex_ballApprox K hKv n)
    (zero_mem_ballApprox K hKzero n) hmn hr).trans
      (measureReal_mono (ballApprox_add_closedBall_subset K n r))

/-- Compact convex Gaussian isoperimetry without any condition on the location
of the origin. An anchor in K is canceled exactly between the two endpoints. -/
theorem compactConvex_gaussian_isoperimetry_general {k : ℕ} (hk : 0 < k)
    (K : Set (EuclideanSpace ℝ (Fin k))) (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hKm : (gaussianMeasure (Fin k)).real K ∈ Ioo (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) :
    Φ (q ((gaussianMeasure (Fin k)).real K)+r) ≤
      (gaussianMeasure (Fin k)).real (K + Metric.closedBall 0 r) := by
  letI : NeZero k := ⟨hk.ne'⟩
  rcases hr.eq_or_lt with rfl | hr
  · simp [Φ_q hKm]
  obtain ⟨b, hb⟩ := nonempty_of_measureReal_ne_zero hKm.1.ne'
  let t : ℕ → ℝ := fun n => 1 / ((n : ℝ)+2)
  let R : ℕ → ℝ := fun n => r*((n : ℝ)+2)
  let S : ℕ → ℝ := fun n => R n-‖b‖
  have ht (n : ℕ) : t n ∈ Ioo (0:ℝ) 1 := by
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    dsimp [t]
    constructor
    · positivity
    · exact (div_lt_one (by positivity)).mpr (by linarith)
  have htlim : Tendsto t atTop (𝓝 (0:ℝ)) := by
    have h := (tendsto_add_atTop_iff_nat 2).mpr (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  have hRlim : Tendsto R atTop atTop := by
    apply Tendsto.const_mul_atTop hr
    simpa only [add_comm] using tendsto_atTop_add_const_left atTop 2
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hSlim : Tendsto S atTop atTop := by
    simpa only [S, sub_eq_add_neg, add_comm] using
      tendsto_atTop_add_const_left atTop (-‖b‖) hRlim
  have htR (n : ℕ) : t n * R n = r := by
    have hn : (n : ℝ)+2 ≠ 0 := by positivity
    dsimp [t, R]
    field_simp
  have htS (n : ℕ) : t n * S n = r-t n*‖b‖ := by
    dsimp only [S]
    rw [mul_sub, htR]
  have htSlim : Tendsto (fun n => t n * S n) atTop (𝓝 r) := by
    simpa only [htS, zero_mul, sub_zero] using
      (tendsto_const_nhds (x := r)).sub (htlim.mul_const ‖b‖)
  have hqtlim : Tendsto
      (fun n => t n * q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (S n))))
      atTop (𝓝 r) := by
    have hratio := (gaussian_ball_quantile_div_tendsto_one (ι := Fin k)).comp hSlim
    have heq : ∀ᶠ n in atTop,
        (t n*S n) * (q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (S n))) / S n) =
          t n * q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (S n))) := by
      filter_upwards [hSlim.eventually_gt_atTop (0:ℝ)] with n hn
      field_simp
    simpa only [mul_one] using (htSlim.mul hratio).congr' heq
  have hlim : Tendsto
      (fun n => Φ ((1-t n)*q ((gaussianMeasure (Fin k)).real K) +
        t n*q ((gaussianMeasure (Fin k)).real (Metric.closedBall 0 (S n)))))
      atTop (𝓝 (Φ (q ((gaussianMeasure (Fin k)).real K)+r))) := by
    have h := (((tendsto_const_nhds (x := (1:ℝ))).sub htlim).mul_const
      (q ((gaussianMeasure (Fin k)).real K))).add hqtlim
    simpa only [Function.comp_def, sub_zero, one_mul] using continuous_Φ.continuousAt.tendsto.comp h
  apply le_of_tendsto hlim
  have hBpos := (gaussian_ball_mass_eventually_ge_cdf (ι := Fin k)
    (a := 0) le_rfl (by norm_num)).filter_mono hSlim
  filter_upwards [hBpos] with n hBn
  let A : Set (EuclideanSpace ℝ (Fin k)) := (1-t n)⁻¹ • (K + {-(t n • b)})
  let B : Set (EuclideanSpace ℝ (Fin k)) := Metric.closedBall b (R n)
  have htp : 0 < 1-t n := by linarith [(ht n).2]
  have hAc : IsCompact A := (hKc.add isCompact_singleton).smul _
  have hAv : Convex ℝ A := (hKv.add (convex_singleton _)).smul _
  have hKA : K ⊆ A := by
    intro x hx
    have hcombo := hKv hx hb htp.le (ht n).1.le (show 1-t n+t n=1 by ring)
    refine ⟨(1-t n) • x, ⟨(1-t n) • x+t n • b, hcombo, -(t n • b), by simp, by abel⟩, ?_⟩
    simp only [smul_smul, inv_mul_cancel₀ htp.ne', one_smul]
  have hAm : (gaussianMeasure (Fin k)).real A ∈ Ioo (0:ℝ) 1 :=
    ⟨hKm.1.trans_le (measureReal_mono hKA), compact_gaussian_mass_lt_one A hAc⟩
  have hSB : Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) (S n) ⊆ B := by
    intro x hx
    have hxnorm : ‖x‖ ≤ R n-‖b‖ := by
      simpa only [S, Metric.mem_closedBall, dist_zero_right] using hx
    change dist x b ≤ R n
    rw [dist_eq_norm]
    exact (norm_sub_le x b).trans (by linarith)
  have hSm : (gaussianMeasure (Fin k)).real (Metric.closedBall 0 (S n)) ∈ Ioo (0:ℝ) 1 :=
    ⟨(Φ_pos (0*S n)).trans_le hBn, gaussian_ball_mass_lt_one (S n)⟩
  have hBm : (gaussianMeasure (Fin k)).real B ∈ Ioo (0:ℝ) 1 :=
    ⟨hSm.1.trans_le (measureReal_mono hSB), compact_gaussian_mass_lt_one B (isCompact_closedBall _ _)⟩
  have heq : mixture A B (1-t n) (t n) = K + Metric.closedBall 0 r := by
    rw [mixture_eq_smul_add]
    dsimp only [A, B]
    rw [smul_smul, mul_inv_cancel₀ htp.ne', one_smul,
      smul_closedBall' (ht n).1.ne' b (R n)]
    simp only [Real.norm_eq_abs, abs_of_pos (ht n).1, htR]
    rw [add_assoc, singleton_add_closedBall]
    simp
  have hmix := compactConvex_gaussian_cdf_mixture A B hAc (isCompact_closedBall _ _)
    hAv (convex_closedBall _ _) hAm hBm htp.le (ht n).1.le (by ring)
  rw [heq] at hmix
  apply le_trans _ hmix
  apply strictMono_Φ.monotone
  have hqA := strictMonoOn_q.monotoneOn hKm hAm (measureReal_mono hKA)
  have hqB := strictMonoOn_q.monotoneOn hSm hBm (measureReal_mono hSB)
  exact add_le_add (mul_le_mul_of_nonneg_left hqA htp.le)
    (mul_le_mul_of_nonneg_left hqB (ht n).1.le)

/-- Closed convex Gaussian isoperimetry with no origin condition. -/
theorem closedConvex_gaussian_isoperimetry_general {k : ℕ} (hk : 0 < k)
    (K : Set (EuclideanSpace ℝ (Fin k))) (hKc : IsClosed K) (hKv : Convex ℝ K)
    (hKm : (gaussianMeasure (Fin k)).real K ∈ Ioo (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) :
    Φ (q ((gaussianMeasure (Fin k)).real K)+r) ≤
      (gaussianMeasure (Fin k)).real (K + Metric.closedBall 0 r) := by
  open ClosedBallApproximation in
  have hmlim := measure_ballApprox_tendsto (gaussianMeasure (Fin k)) K hKc
  have hqlim := (continuousAt_q hKm).tendsto.comp hmlim
  have hlim := continuous_Φ.continuousAt.tendsto.comp (hqlim.add_const r)
  apply le_of_tendsto hlim
  filter_upwards [eventually_measure_ballApprox_mem_Ioo (gaussianMeasure (Fin k)) K hKc hKm]
    with n hmn
  exact (compactConvex_gaussian_isoperimetry_general hk (ballApprox K n)
    (isCompact_ballApprox K hKc n) (convex_ballApprox K hKv n) hmn hr).trans
      (measureReal_mono (ballApprox_add_closedBall_subset K n r))

end OAI.GaussianPropeller
