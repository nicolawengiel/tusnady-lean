import Tusnady.Upper.GaussianBody
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
# Actual finite Euclidean Gaussian measure for the Ehrhard analytic port

The measure is the product of standard one-dimensional Gaussian measures,
transported by `WithLp.toLp 2`. In dimensions indexed by `Fin k` it is
definitionally the measure used in the upper-bound reduction.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal InnerProductSpace
namespace OAI.GaussianPropeller

/-- The standard Gaussian, indexed by an arbitrary finite coordinate type. -/
def gaussianMeasure (ι : Type*) [Fintype ι] : Measure (EuclideanSpace ℝ ι) :=
  (Measure.pi (fun _ : ι => gaussianReal 0 1)).map (WithLp.toLp 2)

instance gaussianMeasure_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (gaussianMeasure ι) := by
  unfold gaussianMeasure
  infer_instance

lemma gaussianMeasure_fin_eq (k : ℕ) :
    gaussianMeasure (Fin k) = Tusnady.Upper.euclideanGaussian k := rfl

lemma gaussianMeasure_integrable_id (ι : Type*) [Fintype ι] :
    Integrable (fun x : EuclideanSpace ℝ ι => x) (gaussianMeasure ι) := by
  apply integrable_piLp_iff.mpr
  intro i
  unfold gaussianMeasure
  have hc : Continuous (fun x : EuclideanSpace ℝ ι => x i) := PiLp.continuous_apply 2 (fun _ : ι => ℝ) i
  apply (integrable_map_measure hc.aestronglyMeasurable (by fun_prop)).mpr
  change Integrable (fun z : ι → ℝ => z i) (Measure.pi (fun _ : ι => gaussianReal 0 1))
  have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 1).integrable le_rfl
  exact ((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).integrable_comp
    hi.aestronglyMeasurable).mpr hi

lemma gaussianMeasure_integrable_exp_inner {ι : Type*} [Fintype ι]
    (h : EuclideanSpace ℝ ι) (t : ℝ) :
    Integrable (fun x => Real.exp (t * inner ℝ h x)) (gaussianMeasure ι) := by
  classical
  unfold gaussianMeasure
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  have hprod := Integrable.fintype_prod
    (fun i : ι => integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (t * h i))
  convert hprod using 1
  funext z
  simp only [Function.comp_def, PiLp.inner_apply, RCLike.inner_apply', conj_trivial,
    PiLp.toLp_apply, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  ring

end OAI.GaussianPropeller
