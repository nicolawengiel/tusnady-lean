import Tusnady.Upper.Ehrhard.GaussianRotation
import Tusnady.Upper.Ehrhard.Quantile
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Moments.Basic

/-!
# Sharp exponential Gaussian norm tails in every fixed finite dimension

The squared-norm exponential moment is proved from the actual Gaussian density
and finite products. This supplies the exponent needed to recover asymptotic
unit slope for Gaussian quantiles of growing balls.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal InnerProductSpace Topology
namespace OAI.GaussianPropeller

lemma gaussian_square_density (t x : ℝ) :
    Real.exp (t*x^2) * gaussianPDFReal 0 1 x =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-(1/2-t)*x^2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_square_exp_integrable {t : ℝ} (ht : t < 1/2) :
    Integrable (fun x : ℝ => Real.exp (t*x^2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1:ℝ≥0) ≠ 0)]
  apply (integrable_withDensity_iff (measurable_gaussianPDF 0 1)
    (ae_of_all _ (fun x => gaussianPDF_lt_top (μ := 0) (v := 1) (x := x)))).mpr
  simp only [gaussianPDF_def, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _)]
  simp_rw [gaussian_square_density]
  exact (integrable_exp_neg_mul_sq (by linarith : 0 < 1/2-t)).const_mul _

lemma gaussian_square_exp_integral {t : ℝ} (ht : t < 1/2) :
    (∫ x : ℝ, Real.exp (t*x^2) ∂gaussianReal 0 1) =
      (Real.sqrt (1-2*t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, mul_comm (gaussianPDFReal 0 1 _) _]
  simp_rw [gaussian_square_density]
  rw [integral_const_mul, integral_gaussian]
  have ht' : 0 < 1/2-t := by linarith
  have hb : 0 < 1-2*t := by linarith
  have hp : 0 < Real.sqrt (2*Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hq : 0 < Real.sqrt (Real.pi/(1/2-t)) := Real.sqrt_pos.mpr (div_pos Real.pi_pos ht')
  have hs : 0 < Real.sqrt (1-2*t) := Real.sqrt_pos.mpr hb
  have hsq : ((Real.sqrt (2*Real.pi))⁻¹ * Real.sqrt (Real.pi/(1/2-t)))^2 =
      ((Real.sqrt (1-2*t))⁻¹)^2 := by
    rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity), inv_pow, Real.sq_sqrt hb.le]
    field_simp
  nlinarith [mul_pos (inv_pos.mpr hp) hq, inv_pos.mpr hs]

lemma gaussian_normSquare_exp_integrable {ι : Type*} [Fintype ι]
    {t : ℝ} (ht : t < 1/2) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (t*‖x‖^2)) (gaussianMeasure ι) := by
  unfold gaussianMeasure
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  have hprod := Integrable.fintype_prod (fun _ : ι => gaussian_square_exp_integrable ht)
  convert hprod using 1
  funext x
  simp only [Function.comp_def, EuclideanSpace.norm_sq_eq, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs, Finset.mul_sum, Real.exp_sum]

/-- The exact squared-norm exponential moment of the actual product Gaussian. -/
theorem gaussian_normSquare_exp_integral {ι : Type*} [Fintype ι]
    {t : ℝ} (ht : t < 1/2) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (t*‖x‖^2) ∂gaussianMeasure ι) =
      ((Real.sqrt (1-2*t))⁻¹)^(Fintype.card ι) := by
  rw [gaussianMeasure, integral_map (by fun_prop) (by fun_prop)]
  simp only [ EuclideanSpace.norm_sq_eq, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs, Finset.mul_sum, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod (μ := fun _ : ι => gaussianReal 0 1)
    (fun _ : ι => fun x : ℝ => Real.exp (t*x^2))]
  simp only [gaussian_square_exp_integral ht, Finset.prod_const, Finset.card_univ]

/-- A sharp-rate exponential tail bound: `t` may approach `1/2` from below. -/
theorem gaussian_norm_tail {ι : Type*} [Fintype ι] {t R : ℝ}
    (ht0 : 0 ≤ t) (ht : t < 1/2) (hR : 0 ≤ R) :
    (gaussianMeasure ι).real {x | R < ‖x‖} ≤
      ((Real.sqrt (1-2*t))⁻¹)^(Fintype.card ι) * Real.exp (-t*R^2) := by
  have h := measure_ge_le_exp_mul_mgf (μ := gaussianMeasure ι)
    (X := fun x : EuclideanSpace ℝ ι => ‖x‖^2) (R^2) ht0
    (gaussian_normSquare_exp_integrable ht)
  rw [mgf, gaussian_normSquare_exp_integral ht] at h
  have hsub : {x : EuclideanSpace ℝ ι | R < ‖x‖} ⊆ {x | R^2 ≤ ‖x‖^2} := by
    intro x hx
    exact (sq_le_sq₀ hR (norm_nonneg x)).mpr hx.le
  exact (measureReal_mono hsub).trans (by simpa only [mul_comm] using h)

namespace Quantile

lemma Φ_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1:ℝ≥0) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  unfold Φ
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

/-- A one-unit interval gives the lower tail rate needed for ball asymptotics. -/
lemma one_sub_Φ_ge_density_add_one {x : ℝ} (hx : 0 ≤ x) :
    φ (x+1) ≤ 1-Φ x := by
  have hbound := setIntegral_ge_of_const_le (μ := volume) (f := φ)
    (c := φ (x+1)) measurableSet_Ioc (by simp) (s := Ioc x (x+1))
    (fun y hy => ?_) integrable_φ.integrableOn
  · have hv : (volume : Measure ℝ).real (Ioc x (x+1)) = 1 := by
      simp [measureReal_def, Real.volume_Ioc]
    rw [hv, one_smul] at hbound
    have hi : (∫ y in Ioc x (x+1), φ y) ≤ ∫ y in Ioi x, φ y :=
      setIntegral_mono_set integrable_φ.integrableOn
        (ae_of_all _ (fun y => (φ_pos y).le))
        (ae_of_all _ (fun y hy => hy.1))
    rw [Φ_eq_one_sub_tail]
    linarith
  · unfold φ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    have hy0 : 0 ≤ y := hx.trans hy.1.le
    nlinarith [hy.2]

end Quantile

lemma eventually_exp_quadratic_le_density {a t C : ℝ}
    (hat : a^2/2 < t) (hC : 0 < C) :
    ∀ᶠ R : ℝ in atTop, C * Real.exp (-t*R^2) ≤ Quantile.φ (a*R+1) := by
  let c := (Real.sqrt (2*Real.pi))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  let δ := t-a^2/2
  have hδ : 0 < δ := sub_pos.mpr hat
  let A := Real.log C-Real.log c+1/2
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop ((a+|A|+1)/δ)] with R hR hlarge
  have hr0 : 0 ≤ R := by linarith
  have hlin : a+|A|+1 ≤ δ*R := by
    have hh := (div_le_iff₀ hδ).mp hlarge
    nlinarith
  have hquad := mul_le_mul_of_nonneg_right hlin hr0
  have habs : |A| ≤ |A| * R := by
    nlinarith [mul_le_mul_of_nonneg_left hR (abs_nonneg A)]
  have hcore : A+a*R ≤ δ*R^2 := by
    nlinarith [le_abs_self A]
  change C * Real.exp (-t*R^2) ≤ c * Real.exp (-(a*R+1)^2/2)
  rw [show C = Real.exp (Real.log C) from (Real.exp_log hC).symm,
    show c = Real.exp (Real.log c) from (Real.exp_log hc).symm,
    ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [δ, A] at hcore
  nlinarith

/-- Every subunit nonnegative linear rate lies eventually below the ball CDF. -/
theorem gaussian_ball_mass_eventually_ge_cdf {ι : Type*} [Fintype ι]
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ∀ᶠ R : ℝ in atTop, Quantile.Φ (a*R) ≤
      (gaussianMeasure ι).real (Metric.closedBall 0 R) := by
  let t := (1+a^2)/4
  have ha2 : a^2 < 1 := by nlinarith
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht : t < 1/2 := by dsimp [t]; linarith
  have hat : a^2/2 < t := by dsimp [t]; linarith
  let C := ((Real.sqrt (1-2*t))⁻¹)^(Fintype.card ι)
  have hC : 0 < C := by
    apply pow_pos
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  filter_upwards [eventually_ge_atTop (0:ℝ),
    eventually_exp_quadratic_le_density hat hC] with R hR hexp
  have htail := gaussian_norm_tail (ι := ι) ht0 ht hR
  have hcompl := measureReal_compl (μ := gaussianMeasure ι)
    (Metric.isClosed_closedBall (x := (0 : EuclideanSpace ℝ ι)) (ε := R)).measurableSet
  have heq : (Metric.closedBall (0 : EuclideanSpace ℝ ι) R)ᶜ = {x | R < ‖x‖} := by
    ext x
    simp [Metric.mem_closedBall, dist_zero_right]
  rw [heq] at hcompl
  simp only [probReal_univ] at hcompl
  rw [hcompl] at htail
  have hphi := Quantile.one_sub_Φ_ge_density_add_one (mul_nonneg ha hR)
  change C * Real.exp (-t*R^2) ≤ _ at hexp
  change 1 - (gaussianMeasure ι).real (Metric.closedBall 0 R) ≤
    C * Real.exp (-t*R^2) at htail
  linarith

/-- A ball is contained in the coordinate halfspace at the same radius. -/
lemma gaussian_ball_mass_le_cdf {ι : Type*} [Fintype ι] [Nonempty ι] (R : ℝ) :
    (gaussianMeasure ι).real (Metric.closedBall 0 R) ≤ Quantile.Φ R := by
  classical
  let i : ι := Classical.choice inferInstance
  let u := EuclideanSpace.basisFun ι ℝ i
  have hu : ‖u‖ = 1 := (EuclideanSpace.basisFun ι ℝ).orthonormal.norm_eq_one i
  have hlaw : (gaussianMeasure ι).map (fun x => inner ℝ u x) = gaussianReal 0 1 := by
    simpa only [hu, one_pow, Real.toNNReal_one] using gaussianMeasure_inner_law u
  have hhalf : (gaussianMeasure ι).real {x | inner ℝ u x ≤ R} = Quantile.Φ R := by
    rw [Quantile.Φ_eq_gaussianReal, ← hlaw]
    simp only [measureReal_def]
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ ι) R ⊆ {x | inner ℝ u x ≤ R} := by
    intro x hx
    have hxnorm : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    exact (real_inner_le_norm u x).trans (by simpa only [hu, one_mul] using hxnorm)
  exact (measureReal_mono hsub).trans_eq hhalf

/-- Positive-dimensional Gaussian balls never have full measure at finite radius. -/
lemma gaussian_ball_mass_lt_one {ι : Type*} [Fintype ι] [Nonempty ι] (R : ℝ) :
    (gaussianMeasure ι).real (Metric.closedBall 0 R) < 1 :=
  (gaussian_ball_mass_le_cdf R).trans_lt (Quantile.Φ_lt_one R)

/-- The lower asymptotic unit slope needed in the Ehrhard-to-isoperimetry
argument. The dimension is fixed while the radius tends to infinity. -/
theorem gaussian_ball_quantile_eventually_ge {ι : Type*} [Fintype ι] [Nonempty ι]
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1) :
    ∀ᶠ R : ℝ in atTop, a*R ≤
      Quantile.q ((gaussianMeasure ι).real (Metric.closedBall 0 R)) := by
  filter_upwards [gaussian_ball_mass_eventually_ge_cdf (ι := ι) ha ha1] with R hR
  have hp : (gaussianMeasure ι).real (Metric.closedBall 0 R) ∈ Ioo (0:ℝ) 1 :=
    ⟨(Quantile.Φ_pos (a*R)).trans_le hR, gaussian_ball_mass_lt_one R⟩
  have h := Quantile.strictMonoOn_q.monotoneOn (Quantile.Φ_mem (a*R)) hp hR
  simpa only [Quantile.q_Φ] using h

theorem gaussian_ball_quantile_eventually_ge_one_sub {ι : Type*} [Fintype ι] [Nonempty ι]
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, (1-ε)*R ≤
      Quantile.q ((gaussianMeasure ι).real (Metric.closedBall 0 R)) := by
  by_cases hε1 : ε < 1
  · exact gaussian_ball_quantile_eventually_ge (by linarith) (by linarith)
  · filter_upwards [eventually_ge_atTop (0:ℝ),
      gaussian_ball_quantile_eventually_ge (ι := ι) (a := 0) le_rfl (by norm_num)] with R hR hq
    simp only [zero_mul] at hq
    exact (mul_nonpos_of_nonpos_of_nonneg (by linarith) hR).trans hq

lemma gaussian_ball_quantile_eventually_le {ι : Type*} [Fintype ι] [Nonempty ι] :
    ∀ᶠ R : ℝ in atTop, Quantile.q ((gaussianMeasure ι).real (Metric.closedBall 0 R)) ≤ R := by
  filter_upwards [gaussian_ball_mass_eventually_ge_cdf (ι := ι) (a := 0) le_rfl
    (by norm_num)] with R hm
  have hp : (gaussianMeasure ι).real (Metric.closedBall 0 R) ∈ Ioo (0:ℝ) 1 :=
    ⟨(Quantile.Φ_pos (0*R)).trans_le hm, gaussian_ball_mass_lt_one R⟩
  have h := Quantile.strictMonoOn_q.monotoneOn hp (Quantile.Φ_mem R) (gaussian_ball_mass_le_cdf R)
  simpa only [Quantile.q_Φ] using h

/-- The exact asymptotic slope, for each fixed positive finite dimension. -/
theorem gaussian_ball_quantile_div_tendsto_one {ι : Type*} [Fintype ι] [Nonempty ι] :
    Tendsto (fun R : ℝ => Quantile.q ((gaussianMeasure ι).real (Metric.closedBall 0 R)) / R)
      atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [eventually_ge_atTop (1:ℝ),
    gaussian_ball_quantile_eventually_ge_one_sub (ι := ι) (show 0 < ε/2 by linarith),
    gaussian_ball_quantile_eventually_le (ι := ι)] with R hR hlo hhi
  have hr : 0 < R := by linarith
  have hlo' : 1-ε/2 ≤ Quantile.q ((gaussianMeasure ι).real (Metric.closedBall 0 R))/R :=
    (le_div_iff₀ hr).mpr hlo
  have hhi' : Quantile.q ((gaussianMeasure ι).real (Metric.closedBall 0 R))/R ≤ 1 :=
    (div_le_iff₀ hr).mpr (by simpa only [one_mul] using hhi)
  rw [Real.dist_eq, abs_of_nonpos (by linarith :
    Quantile.q ((gaussianMeasure ι).real (Metric.closedBall 0 R))/R-1 ≤ 0)]
  linarith

end OAI.GaussianPropeller
