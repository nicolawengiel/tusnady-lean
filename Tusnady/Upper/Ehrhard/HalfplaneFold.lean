import Tusnady.Upper.Ehrhard.GaussianTailBounds
import Tusnady.Upper.Ehrhard.GaussianScalar
import Tusnady.Upper.Ehrhard.SmallRadiusQuantile
import Tusnady.Upper.Ehrhard.GaussianBallAsymptotics
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Gaussian cone estimate in the half-plane fold

All integrals use the actual product of two standard real Gaussian measures.
The cone loss is bounded using Mills' inequality and an exact quadratic
identity. Affine Gaussian integration is proved by the fundamental theorem of
calculus, so no change-of-variables premise is introduced.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace OAI.GaussianPropeller.HalfplaneFold
open Quantile

abbrev gaussianProduct : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1)

def cone (c s D cut : ℝ) : Set (ℝ × ℝ) :=
  {p | cut < p.1 ∧ c * p.1 + s * p.2 ≤ D}

def region (c s D cut : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ cut ∧ c * p.1 + s * p.2 ≤ D}

lemma measurableSet_cone (c s D cut : ℝ) : MeasurableSet (cone c s D cut) := by
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_le (show Measurable (fun p : ℝ × ℝ => c*p.1+s*p.2) by fun_prop)
      measurable_const)

lemma product_real_sections (K : Set (ℝ × ℝ)) (hK : MeasurableSet K) :
    gaussianProduct.real K = ∫ x, (gaussianReal 0 1).real {y | (x, y) ∈ K} ∂gaussianReal 0 1 := by
  rw [measureReal_def, Measure.prod_apply hK]
  symm
  exact integral_toReal (measurable_measure_prodMk_left hK).aemeasurable
    (ae_of_all _ (fun _ => measure_lt_top _ _))

lemma cone_mass_eq_integral (c D cut : ℝ) {s : ℝ} (hs : 0 < s) :
    gaussianProduct.real (cone c s D cut) =
      ∫ x in Ioi cut, Φ (-((c*x-D)/s)) * φ x := by
  have hsec (x : ℝ) : {y | (x, y) ∈ cone c s D cut} =
      if cut < x then Iic ((D-c*x)/s) else ∅ := by
    ext y
    by_cases hx : cut < x
    · simp [cone, hx]
      rw [le_div_iff₀ hs]
      constructor <;> intro h <;> nlinarith
    · simp [cone, hx]
  calc
    _ = ∫ x, if cut < x then Φ ((D-c*x)/s) else 0 ∂gaussianReal 0 1 := by
      rw [product_real_sections _ (measurableSet_cone c s D cut)]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hsec]
      by_cases hx : cut < x <;> simp [hx, ← Φ_eq_gaussianReal]
    _ = _ := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards [] with x
      have hpdf : gaussianPDFReal 0 1 x = φ x := by
        simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]
      have harg : (D-c*x)/s = -((c*x-D)/s) := by ring
      by_cases hx : cut < x
      · simp [hx, hpdf, harg, mul_comm]
      · simp [hx, hpdf]

private lemma affine_primitive_deriv {s : ℝ} (hs : 0 < s) (b x : ℝ) :
    HasDerivAt (fun x : ℝ => s * Φ ((x-b)/s)) (φ ((x-b)/s)) x := by
  have hi := ((hasDerivAt_id x).sub_const b).div_const s
  have h := ((hasDerivAt_Φ ((x-b)/s)).comp x hi).const_mul s
  convert h using 1 <;> first | rfl | (field_simp [hs.ne'])

private lemma affine_primitive_tendsto {s : ℝ} (hs : 0 < s) (b : ℝ) :
    Tendsto (fun x : ℝ => s * Φ ((x-b)/s)) atTop (𝓝 s) := by
  have hbase : Tendsto (fun x : ℝ => x-b) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    filter_upwards [eventually_ge_atTop (M+b)] with x hx
    linarith
  have hz : Tendsto (fun x : ℝ => (x-b)/s) atTop atTop := hbase.atTop_div_const hs
  simpa only [mul_one, Function.comp_def] using (tendsto_Φ_atTop.comp hz).const_mul s

lemma affine_tail_integrable {s : ℝ} (hs : 0 < s) (b cut : ℝ) :
    IntegrableOn (fun x : ℝ => φ ((x-b)/s)) (Ioi cut) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun x _ => affine_primitive_deriv hs b x) (fun x _ => (φ_pos _).le)
    (affine_primitive_tendsto hs b)

lemma affine_tail_integral {s : ℝ} (hs : 0 < s) (b cut : ℝ) :
    (∫ x in Ioi cut, φ ((x-b)/s)) = s * Φ (-((cut-b)/s)) := by
  have hi := integral_Ioi_of_hasDerivAt_of_nonneg' (a := cut)
    (fun x _ => affine_primitive_deriv hs b x) (fun x _ => (φ_pos _).le)
    (affine_primitive_tendsto hs b)
  rw [Φ_neg]
  nlinarith

lemma cone_density_integrable (c s D : ℝ) :
    Integrable (fun x : ℝ => Φ (-((c*x-D)/s)) * φ x) := by
  apply Integrable.mono' integrable_φ
    (((continuous_Φ.comp (show Continuous (fun x : ℝ => -((c*x-D)/s)) by fun_prop)).mul
      continuous_φ).aestronglyMeasurable)
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply,
    abs_of_pos (mul_pos (Φ_pos _) (φ_pos _))]
  exact mul_le_of_le_one_left (φ_pos x).le (Φ_lt_one _).le

/-- Rotation of the quadratic form is an exact polynomial identity. -/
lemma density_product_identity (c s D x : ℝ) (hs : s ≠ 0) (hunit : c^2+s^2=1) :
    φ ((c*x-D)/s) * φ x = φ D * φ ((x-c*D)/s) := by
  have hquad : ((c*x-D)/s)^2+x^2 = ((x-c*D)/s)^2+D^2 := by
    field_simp [hs]
    linear_combination (x^2-D^2) * hunit
  have hexp : -((c*x-D)/s)^2/2 + -x^2/2 = -D^2/2 + -((x-c*D)/s)^2/2 := by
    nlinarith [hquad]
  unfold φ
  calc
    _ = (((Real.sqrt (2*Real.pi))⁻¹)^2) *
        (Real.exp (-((c*x-D)/s)^2/2) * Real.exp (-x^2/2)) := by ring
    _ = (((Real.sqrt (2*Real.pi))⁻¹)^2) *
        (Real.exp (-D^2/2) * Real.exp (-((x-c*D)/s)^2/2)) := by
      rw [← Real.exp_add, ← Real.exp_add, hexp]
    _ = _ := by ring

/-- The Gaussian cone loss is controlled by a one-dimensional tail. -/
theorem cone_mass_le (c s D cut a : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (ha : 0 < a)
    (hycut : a ≤ (c*cut-D)/s) (hzcut : a ≤ (cut-c*D)/s) :
    gaussianProduct.real (cone c s D cut) ≤ s * φ D * Φ (-a) / a := by
  rw [cone_mass_eq_integral c D cut hs]
  calc
    _ ≤ ∫ x in Ioi cut, (φ D / a) * φ ((x-c*D)/s) := by
      apply integral_mono_ae (cone_density_integrable c s D).integrableOn
        ((affine_tail_integrable hs (c*D) cut).const_mul (φ D/a))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hy : a ≤ (c*x-D)/s := hycut.trans
        (div_le_div_of_nonneg_right (sub_le_sub_right
          (mul_le_mul_of_nonneg_left hx.le hc.le) D) hs.le)
      have ht := (gaussian_tail_le_density_div (ha.trans_le hy)).trans
        (div_le_div_of_nonneg_left (φ_pos _).le ha hy)
      calc
        _ ≤ (φ ((c*x-D)/s) / a) * φ x := mul_le_mul_of_nonneg_right ht (φ_pos x).le
        _ = (φ D / a) * φ ((x-c*D)/s) := by
          rw [div_mul_eq_mul_div, density_product_identity c s D x hs.ne' hunit]
          ring
    _ = (φ D/a) * (s * Φ (-((cut-c*D)/s))) := by
      rw [integral_const_mul, affine_tail_integral hs (c*D) cut]
    _ ≤ (φ D/a) * (s * Φ (-a)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (strictMono_Φ.monotone (neg_le_neg hzcut)) hs.le) (div_nonneg (φ_pos D).le ha.le)
    _ = _ := by ring

lemma density_antitone_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : φ y ≤ φ x := by
  unfold φ
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hsq := pow_le_pow_left₀ hx hxy 2
  nlinarith

/-- The translated half-plane gains at least the density at its new boundary
multiplied by the displacement. -/
lemma cdf_shift_gain {d D : ℝ} (hd : 0 ≤ d) (hD : d ≤ D) :
    (D-d) * φ D ≤ Φ D - Φ d := by
  have hv : (volume : Measure ℝ).real (Ioc d D) = D-d := by
    simp only [measureReal_def, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hD)]
  have hb := setIntegral_ge_of_const_le (μ := volume) (f := φ)
    (c := φ D) (s := Ioc d D) measurableSet_Ioc (by simp)
    (fun x hx => density_antitone_nonneg (hd.trans hx.1.le) hx.2) integrable_φ.integrableOn
  have hi := intervalIntegral.integral_Iic_sub_Iic (a := d) (b := D)
    integrable_φ.integrableOn integrable_φ.integrableOn
  change Φ D - Φ d = _ at hi
  rw [intervalIntegral.integral_of_le hD] at hi
  rw [hv, ← hi] at hb
  simpa only [smul_eq_mul, mul_comm] using hb

/-- The geometric cutoffs put both Gaussian tail coordinates above w-r. -/
lemma cutoff_geometry (c s d r w : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (hd : 0 ≤ d) (hr : 0 < r) (hwr : r < w) :
    (w-r) ≤ (c*((d+s*w)/c)-(d+r*s))/s ∧
      (w-r) ≤ (((d+s*w)/c)-c*(d+r*s))/s := by
  have hy : (c*((d+s*w)/c)-(d+r*s))/s = w-r := by
    field_simp [hc.ne', hs.ne'] <;> ring
  refine ⟨hy.ge, ?_⟩
  have hz : (((d+s*w)/c)-c*(d+r*s))/s = ((w-r)+s*(d+r*s))/c := by
    field_simp [hc.ne', hs.ne']
    linear_combination -(d+r*s) * hunit
  rw [hz]
  have ha : 0 < w-r := sub_pos.mpr hwr
  have hD : 0 ≤ d+r*s := add_nonneg hd (mul_nonneg hr.le hs.le)
  have hc1 : c ≤ 1 := by nlinarith [sq_nonneg s, sq_nonneg (c-1)]
  apply (le_div_iff₀ hc).mpr
  have hm := mul_le_mul_of_nonneg_left hc1 ha.le
  nlinarith [mul_nonneg hs.le hD]

/-- The two-dimensional half-plane estimate. Its scalar condition is explicit
and is proved for actual Gaussian interval quantiles in SmallRadiusQuantile.
There is no unproved analytic or literature assumption in this theorem. -/
theorem halfplane_fold_mass (c s d r w : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (hd : 0 ≤ d) (hr : 0 < r) (hwr : r < w)
    (hscalar : Φ (-w+r) ≤ r*(w-r)) :
    Φ d ≤ gaussianProduct.real
      {p : ℝ × ℝ | p.1 ≤ (d+s*w)/c ∧ c*p.1+s*p.2 ≤ d+r*s} := by
  have ha : 0 < w-r := sub_pos.mpr hwr
  obtain ⟨hycut, hzcut⟩ := cutoff_geometry c s d r w hc hs hunit hd hr hwr
  have hcone := cone_mass_le c s (d+r*s) ((d+s*w)/c) (w-r) hc hs hunit ha hycut hzcut
  have htail : Φ (-(w-r))/(w-r) ≤ r := by
    apply (div_le_iff₀ ha).mpr
    simpa only [show -(w-r) = -w+r by ring] using hscalar
  have hconebound : gaussianProduct.real (cone c s (d+r*s) ((d+s*w)/c)) ≤
      r*s*φ (d+r*s) := by
    calc
      _ ≤ s*φ (d+r*s)*Φ (-(w-r))/(w-r) := hcone
      _ = (s*φ (d+r*s))*(Φ (-(w-r))/(w-r)) := by ring
      _ ≤ (s*φ (d+r*s))*r := mul_le_mul_of_nonneg_left htail
        (mul_nonneg hs.le (φ_pos _).le)
      _ = _ := by ring
  have hgain : r*s*φ (d+r*s) ≤ Φ (d+r*s)-Φ d := by
    have hh := cdf_shift_gain hd (show d ≤ d+r*s by nlinarith [mul_pos hr hs])
    convert hh using 1 <;> ring
  have heq : {p : ℝ × ℝ | p.1 ≤ (d+s*w)/c ∧ c*p.1+s*p.2 ≤ d+r*s} =
      {p : ℝ × ℝ | c*p.1+s*p.2 ≤ d+r*s} \ cone c s (d+r*s) ((d+s*w)/c) := by
    ext p
    constructor
    · rintro ⟨hx, hlin⟩
      exact ⟨hlin, fun h => (not_lt_of_ge hx) h.1⟩
    · rintro ⟨hlin, hnot⟩
      exact ⟨le_of_not_gt (fun h => hnot ⟨h, hlin⟩), hlin⟩
  rw [heq]
  rw [measureReal_diff (μ := gaussianProduct)
    (s₁ := {p : ℝ × ℝ | c*p.1+s*p.2 ≤ d+r*s})
    (s₂ := cone c s (d+r*s) ((d+s*w)/c)) (fun p hp => hp.2)
    (measurableSet_cone c s (d+r*s) ((d+s*w)/c))]
  rw [gaussianProduct_halfspace_mass c s hunit (d+r*s)]
  linarith

/-- The scalar hypothesis is discharged for the actual centered interval
quantile, using the explicitly proved universal radius 1/1000. -/
theorem halfplane_fold_mass_of_small_radius (c s d r : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hunit : c^2+s^2=1) (hd : 0 ≤ d) (hr : 0 < r) (hsmall : r ≤ (1 : ℝ)/1000) :
    let w := -q ((gaussianReal 0 1).real (Icc (-r) r))
    Φ d ≤ gaussianProduct.real
      {p : ℝ × ℝ | p.1 ≤ (d+s*w)/c ∧ c*p.1+s*p.2 ≤ d+r*s} := by
  dsimp only
  obtain ⟨hp, hw, hscalar⟩ := SmallRadiusQuantile.small_radius_quantile hr hsmall
  exact halfplane_fold_mass c s d r _ hc hs hunit hd hr (by linarith) hscalar

end OAI.GaussianPropeller.HalfplaneFold
