import Tusnady.GaussianMarginals
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Gaussian concentration used in Nikolov §4. The Gaussian moment-generating
function and Chernoff bound come from the pinned mathlib. Both tails and
zero variance are included; the positive proxy B avoids division by variance.
-/
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace Tusnady.Upper

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma gaussian_exp_integrable {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) (t : ℝ) :
    Integrable (fun z => Real.exp (t * X z)) μ := by
  apply mgf_pos_iff.mp
  rw [mgf_gaussianReal hX t]
  exact Real.exp_pos _

/-- Upper Gaussian tail under an upper bound on variance. -/
theorem gaussian_upper_tail {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) {B R : ℝ}
    (hB : 0 < B) (hR : 0 ≤ R) (hv : (v : ℝ) ≤ B^2) :
    μ.real {z | R ≤ X z} ≤ Real.exp (-R^2/(2*B^2)) := by
  let t := R / B^2
  have ht : 0 ≤ t := div_nonneg hR (sq_nonneg B)
  have hb : B^2 ≠ 0 := pow_ne_zero _ hB.ne'
  have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := X) R ht (gaussian_exp_integrable hX t)
  rw [mgf_gaussianReal hX t, zero_mul, zero_add, ← Real.exp_add] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  calc
    -t*R + (v:ℝ)*t^2/2 ≤ -t*R + B^2*t^2/2 := by gcongr
    _ = -R^2/(2*B^2) := by dsimp [t]; field_simp; ring

/-- Lower Gaussian tail, with the same bound and without a nonzero variance premise. -/
theorem gaussian_lower_tail {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) {B R : ℝ}
    (hB : 0 < B) (hR : 0 ≤ R) (hv : (v : ℝ) ≤ B^2) :
    μ.real {z | X z ≤ -R} ≤ Real.exp (-R^2/(2*B^2)) := by
  let t := -R / B^2
  have ht : t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg B)
  have h := measure_le_le_exp_mul_mgf (μ := μ) (X := X) (-R) ht (gaussian_exp_integrable hX t)
  rw [mgf_gaussianReal hX t, zero_mul, zero_add, ← Real.exp_add] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  calc
    -t*(-R) + (v:ℝ)*t^2/2 ≤ -t*(-R) + B^2*t^2/2 := by gcongr
    _ = -R^2/(2*B^2) := by dsimp [t]; field_simp; ring

/-- The simultaneous two-sided tail, in real-valued probability notation. -/
theorem gaussian_abs_tail {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) μ) {B R : ℝ}
    (hB : 0 < B) (hR : 0 ≤ R) (hv : (v : ℝ) ≤ B^2) :
    μ.real {z | R ≤ |X z|} ≤ 2*Real.exp (-R^2/(2*B^2)) := by
  have heq : {z | R ≤ |X z|} = {z | R ≤ X z} ∪ {z | X z ≤ -R} := by
    ext z
    simp only [mem_setOf_eq, mem_union, le_abs]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [heq]
  have hu := measureReal_union_le (μ := μ) {z | R ≤ X z} {z | X z ≤ -R}
  have hr := gaussian_upper_tail hX hB hR hv
  have hl := gaussian_lower_tail hX hB hR hv
  linarith

/-- A genuine finite Gaussian linear form, rather than an assumed marginal law. -/
def gaussianLinearForm {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) (z : Fin k → ℝ) : ℝ :=
  ∑ i, u i * z i

lemma gaussianLinearForm_measurable {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) :
    Measurable (gaussianLinearForm u) := by
  unfold gaussianLinearForm
  fun_prop

lemma gaussianLinearForm_law {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) :
    (Literature.standardGaussian k).map (gaussianLinearForm u) =
      gaussianReal 0 (∑ i, (⟨(u i)^2, sq_nonneg _⟩ : ℝ≥0)) :=
  GaussianMarginals.standardGaussian_sum_law (fun i => u i) Finset.univ

lemma gaussianLinearForm_variance {k : ℕ} (u : EuclideanSpace ℝ (Fin k)) :
    ((∑ i, (⟨(u i)^2, sq_nonneg _⟩ : ℝ≥0)) : ℝ) = ‖u‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,
    Real.norm_eq_abs, sq_abs]

/-- Gaussian linear-form tails controlled by the actual Euclidean row norm. -/
theorem gaussian_linearForm_tail {k : ℕ} (u : EuclideanSpace ℝ (Fin k))
    {B R : ℝ} (hB : 0 < B) (hu : ‖u‖ ≤ B) (hR : 0 ≤ R) :
    (Literature.standardGaussian k).real {z | R < |gaussianLinearForm u z|} ≤
      2*Real.exp (-R^2/(2*B^2)) := by
  letI : IsProbabilityMeasure (Literature.standardGaussian k) := by
    unfold Literature.standardGaussian
    infer_instance
  have hv : ((∑ i, (⟨(u i)^2, sq_nonneg _⟩ : ℝ≥0)) : ℝ) ≤ B^2 := by
    rw [gaussianLinearForm_variance]
    nlinarith [norm_nonneg u]
  have hlaw : HasLaw (gaussianLinearForm u)
      (gaussianReal 0 (∑ i, (⟨(u i)^2, sq_nonneg _⟩ : ℝ≥0)))
      (Literature.standardGaussian k) :=
    ⟨(gaussianLinearForm_measurable u).aemeasurable, gaussianLinearForm_law u⟩
  have hp := gaussian_abs_tail hlaw hB hR (by
    rw [NNReal.coe_sum]
    exact hv)
  have hs : {z : Fin k → ℝ | R < |gaussianLinearForm u z|} ⊆
      {z : Fin k → ℝ | R ≤ |gaussianLinearForm u z|} := by
    intro z hz
    exact (show R < |gaussianLinearForm u z| from hz).le
  exact (measureReal_mono hs).trans hp

end Tusnady.Upper
