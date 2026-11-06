import Tusnady.Upper.Ehrhard.HalfplaneFold
import Mathlib.MeasureTheory.Group.Integral

/-!
# Translating Gaussian cones away from the origin

The cones used in the planar fold comparison have nonnegative horizontal
cutoff. Translating such a cone to the right cannot increase its Gaussian
mass. This follows from an exact translation of the one-dimensional section
integral and the monotonicity of the standard Gaussian density on `[0, ∞)`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace OAI.GaussianPropeller.ConeTranslation
open Quantile HalfplaneFold

/-- Translation of a Lebesgue integral over a right half-line. -/
lemma integral_Ioi_add_shift (f : ℝ → ℝ) (cut δ : ℝ) :
    (∫ x in Ioi (cut + δ), f x) = ∫ x in Ioi cut, f (x + δ) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  calc
    _ = ∫ x : ℝ, (Ioi (cut + δ)).indicator f (x + δ) :=
      (integral_add_right_eq_self _ δ).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [indicator_apply, mem_Ioi, add_lt_add_iff_right]

/-- Moving a cone with nonnegative cutoff to the right decreases its actual
product Gaussian mass. The half-plane boundary moves by the same vector. -/
theorem cone_shift_le (c s D cut δ : ℝ) (hs : 0 < s)
    (hcut : 0 ≤ cut) (hδ : 0 ≤ δ) :
    gaussianProduct.real (cone c s (D + c*δ) (cut + δ)) ≤
      gaussianProduct.real (cone c s D cut) := by
  rw [cone_mass_eq_integral c (D+c*δ) (cut+δ) hs,
    cone_mass_eq_integral c D cut hs, integral_Ioi_add_shift]
  have harg (x : ℝ) : (c*(x+δ)-(D+c*δ))/s = (c*x-D)/s := by ring
  simp_rw [harg]
  have hleft : Integrable (fun x : ℝ => Φ (-((c*x-D)/s)) * φ (x+δ)) := by
    apply Integrable.mono' (integrable_φ.comp_add_right δ)
      (((continuous_Φ.comp (show Continuous (fun x : ℝ => -((c*x-D)/s)) by fun_prop)).mul
        (continuous_φ.comp (show Continuous (fun x : ℝ => x+δ) by fun_prop))).aestronglyMeasurable)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Pi.mul_apply]
    simp only [Function.comp_apply]
    rw [abs_of_pos (mul_pos (Φ_pos _) (φ_pos _))]
    exact mul_le_of_le_one_left (φ_pos _).le (Φ_lt_one _).le
  apply integral_mono_ae hleft.integrableOn (cone_density_integrable c s D).integrableOn
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  apply mul_le_mul_of_nonneg_left _ (Φ_pos _).le
  exact density_antitone_nonneg (hcut.trans hx.le) (le_add_of_nonneg_right hδ)

/-- The cone comparison in the supporting-half-plane reduction. No unit-normal
or radius bound is needed for this translation step. -/
theorem supporting_cone_mass_le (c s D d r w : ℝ) (hc : 0 < c) (hs : 0 < s)
    (hd : 0 ≤ d) (hDd : d ≤ D) (hw : 0 ≤ w) :
    gaussianProduct.real (cone c s (D+r*s) ((D+s*w)/c)) ≤
      gaussianProduct.real (cone c s (d+r*s) ((d+s*w)/c)) := by
  have hδ : 0 ≤ (D-d)/c := div_nonneg (sub_nonneg.mpr hDd) hc.le
  have hcut : 0 ≤ (d+s*w)/c :=
    div_nonneg (add_nonneg hd (mul_nonneg hs.le hw)) hc.le
  have hbound : d+r*s+c*((D-d)/c) = D+r*s := by field_simp; ring
  have hcutoff : (d+s*w)/c+(D-d)/c = (D+s*w)/c := by ring
  simpa only [hbound, hcutoff] using
    cone_shift_le c s (d+r*s) ((d+s*w)/c) ((D-d)/c) hs hcut hδ

end OAI.GaussianPropeller.ConeTranslation
