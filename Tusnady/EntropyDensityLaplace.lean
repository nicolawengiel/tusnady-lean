import Tusnady.EntropyDensity
import Tusnady.Gini
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! # Laplace maximum entropy for actual real densities -/

open MeasureTheory Set Real

namespace Tusnady

/-- The real Laplace density with center `a` and positive scale `beta`. -/
noncomputable def laplaceDensity (a beta x : ℝ) : ℝ :=
  (2 * beta)⁻¹ * Real.exp (-|x - a| / beta)

theorem laplaceDensity_pos {a beta x : ℝ} (hbeta : 0 < beta) :
    0 < laplaceDensity a beta x := by
  unfold laplaceDensity
  positivity

theorem measurable_laplaceDensity (a beta : ℝ) : Measurable (laplaceDensity a beta) := by
  unfold laplaceDensity
  fun_prop

theorem integral_laplaceDensity {a beta : ℝ} (hbeta : 0 < beta) :
    (∫ x, laplaceDensity a beta x) = 1 := by
  have hraw : (∫ x : ℝ, Real.exp (-|x| / beta)) = 2 * beta := by
    have hneg : -beta⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hbeta)
    calc
      _ = 2 * ∫ x : ℝ in Ioi 0, Real.exp (-x / beta) := integral_comp_abs
      _ = 2 * beta := by
        have heq : (fun x : ℝ => Real.exp (-x / beta)) =
            fun x => Real.exp ((-beta⁻¹) * x) := by
          funext x
          congr 1
          ring
        rw [heq, integral_exp_mul_Ioi hneg 0]
        simp
  have hshift : (∫ x : ℝ, Real.exp (-|x - a| / beta)) = 2 * beta := by
    rw [integral_sub_right_eq_self (fun x : ℝ => Real.exp (-|x| / beta)) a]
    exact hraw
  unfold laplaceDensity
  rw [integral_const_mul, hshift]
  exact inv_mul_cancel₀ (mul_ne_zero (by norm_num) hbeta.ne')

theorem integrable_laplaceDensity {a beta : ℝ} (hbeta : 0 < beta) :
    Integrable (laplaceDensity a beta) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_laplaceDensity hbeta]
  exact one_ne_zero

theorem log_laplaceDensity {a beta x : ℝ} (hbeta : 0 < beta) :
    Real.log (laplaceDensity a beta x) = -Real.log (2 * beta) - |x - a| / beta := by
  unfold laplaceDensity
  rw [Real.log_mul (inv_ne_zero (mul_ne_zero (by norm_num) hbeta.ne')) (Real.exp_ne_zero _),
    Real.log_inv, Real.log_exp]
  ring

/-- Laplace maximum entropy with an arbitrary center. This theorem proves
the classical inequality for the concrete entropy integral; it has no
free entropy variable and no Gibbs hypothesis. -/
theorem densityEntropy_le_log_deviation (f : ℝ → ℝ) {a beta : ℝ}
    (hbeta : 0 < beta) (hf : ∀ x, 0 ≤ f x)
    (hfi : Integrable f) (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hdev : Integrable (fun x => f x * |x - a|))
    (hfnorm : (∫ x, f x) = 1) (hbetaeq : (∫ x, f x * |x - a|) = beta) :
    densityEntropy volume f ≤ Real.log (2 * Real.exp 1 * beta) := by
  have hpoint (x : ℝ) : f x * Real.log (laplaceDensity a beta x) =
      -Real.log (2 * beta) * f x - beta⁻¹ * (f x * |x - a|) := by
    rw [log_laplaceDensity hbeta]
    ring
  have hcross : Integrable (fun x => f x * Real.log (laplaceDensity a beta x)) := by
    simp_rw [hpoint]
    exact (hfi.const_mul _).sub (hdev.const_mul _)
  have hgibbs := densityEntropy_le_crossEntropy volume f (laplaceDensity a beta)
    (Filter.Eventually.of_forall hf)
    (Filter.Eventually.of_forall fun _ => laplaceDensity_pos hbeta)
    hfi (integrable_laplaceDensity hbeta) hflog hcross hfnorm (integral_laplaceDensity hbeta)
  have heval : -(∫ x, f x * Real.log (laplaceDensity a beta x)) =
      Real.log (2 * beta) + 1 := by
    simp_rw [hpoint]
    rw [integral_sub (hfi.const_mul _) (hdev.const_mul _), integral_const_mul,
      integral_const_mul, hfnorm, hbetaeq, mul_one, inv_mul_cancel₀ hbeta.ne']
    ring
  have hlog : Real.log (2 * Real.exp 1 * beta) = Real.log (2 * beta) + 1 := by
    have hid : 2 * Real.exp 1 * beta = (2 * beta) * Real.exp 1 := by ring
    rw [hid, Real.log_mul (mul_ne_zero (by norm_num) hbeta.ne') (Real.exp_ne_zero _),
      Real.log_exp]
  rw [heval] at hgibbs
  rwa [hlog]

/-- The scalar entropy-to-CDF correlation bound for an actual real
Lebesgue density. Its exponent is the concrete differential entropy,
and all ingredients (Gibbs, Laplace, Gini and mean deviation) are proved.
No entropy value or entropy inequality is supplied as an input. -/
theorem density_cdf_correlation_lower_bound (f : ℝ → ℝ)
    (hfm : Measurable f) (hf : ∀ x, 0 ≤ f x) (hfi : Integrable f)
    (hfnorm : (∫ x, f x) = 1)
    (hflog : Integrable (fun x => f x * Real.log (f x)))
    (hfirst : Integrable (fun x => f x * x)) :
    Real.exp (densityEntropy volume f) / (4 * Real.exp 1) ≤
      ∫ x, x * (2 * ProbabilityTheory.cdf (realDensityMeasure volume f) x - 1)
        ∂realDensityMeasure volume f := by
  let μ := realDensityMeasure volume f
  haveI : IsProbabilityMeasure μ :=
    isProbabilityMeasure_realDensityMeasure volume f hfm hf hfi hfnorm
  haveI : NoAtoms μ := by
    change NoAtoms (volume.withDensity (fun x => ENNReal.ofReal (f x)))
    infer_instance
  have hid : Integrable (fun x : ℝ => x) μ :=
    (integrable_realDensityMeasure_iff volume f (fun x => x) hfm hf).mpr hfirst
  let a : ℝ := ∫ x, x ∂μ
  let beta : ℝ := ∫ x, |x - a| ∂μ
  have hbeta : 0 < beta := absolute_deviation_pos μ hid a
  have hdevLaw : Integrable (fun x : ℝ => |x - a|) μ := by
    simpa only [Real.norm_eq_abs] using (hid.sub (integrable_const a)).norm
  have hdev : Integrable (fun x => f x * |x - a|) :=
    (integrable_realDensityMeasure_iff volume f (fun x => |x - a|) hfm hf).mp hdevLaw
  have hbetaeq : (∫ x, f x * |x - a|) = beta :=
    (integral_realDensityMeasure volume f (fun x => |x - a|) hfm hf).symm
  have hentropy := densityEntropy_le_log_deviation f hbeta hf hfi hflog hdev hfnorm hbetaeq
  exact scalar_cdf_correlation_of_entropy_bound μ hid (densityEntropy volume f) hentropy

end Tusnady
