import Tusnady.HaarPrimitiveCongruence
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The actual anchored box primitive as a contraction on cube L²

Measurability follows from the measurable joint box kernel. The contraction
bound is proved by integration, using probability-measure L² to L¹ inclusion.
The resulting continuous linear map represents the existing boxPrimitive.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open scoped BigOperators
variable {d : ℕ}

def primitiveKernelSet (d : ℕ) : Set (Tusnady.Point d × Tusnady.Point d) :=
  {z | z.2 ∈ Tusnady.upperBox z.1}

lemma measurableSet_primitiveKernel (d : ℕ) : MeasurableSet (primitiveKernelSet d) := by
  have h : MeasurableSet {z : Tusnady.Point d × Tusnady.Point d |
      ∀ k, z.1 k ≤ z.2 k ∧ z.2 k ≤ 1} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro k
    exact (measurableSet_le ((measurable_pi_apply k).comp measurable_fst)
      ((measurable_pi_apply k).comp measurable_snd)).inter
      (measurableSet_le ((measurable_pi_apply k).comp measurable_snd) measurable_const)
  simpa only [primitiveKernelSet, Tusnady.upperBox, Set.mem_pi, Set.mem_univ,
    true_imp_iff, Set.mem_Icc] using h

def primitiveRepresentative (f : Lp ℝ 2 (cubeMeasure d)) (p : Tusnady.Point d) : ℝ :=
  ∫ x in Tusnady.upperBox p, f x ∂cubeMeasure d

lemma primitiveRepresentative_stronglyMeasurable (f : Lp ℝ 2 (cubeMeasure d)) :
    StronglyMeasurable (primitiveRepresentative f) := by
  have hk : StronglyMeasurable ((primitiveKernelSet d).indicator
      (fun z : Tusnady.Point d × Tusnady.Point d => f z.2)) :=
    ((Lp.stronglyMeasurable f).comp_measurable measurable_snd).indicator (measurableSet_primitiveKernel d)
  have hi := hk.integral_prod_right' (ν := cubeMeasure d)
  have heq : (fun p => ∫ x, (primitiveKernelSet d).indicator
      (fun z : Tusnady.Point d × Tusnady.Point d => f z.2) (p,x) ∂cubeMeasure d) =
      primitiveRepresentative f := by
    funext p
    unfold primitiveRepresentative
    rw [← integral_indicator (Tusnady.upperBox_measurable p)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      by_cases hx : x ∈ Tusnady.upperBox p <;> simp [primitiveKernelSet, hx]
  rwa [heq] at hi

lemma integral_norm_le_L2_norm (f : Lp ℝ 2 (cubeMeasure d)) :
    (∫ x, ‖f x‖ ∂cubeMeasure d) ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable f)

lemma primitiveRepresentative_norm_le (f : Lp ℝ 2 (cubeMeasure d)) (p : Tusnady.Point d) :
    ‖primitiveRepresentative f p‖ ≤ ‖f‖ := by
  rw [primitiveRepresentative, ← integral_indicator (Tusnady.upperBox_measurable p)]
  calc
    _ ≤ ∫ x, ‖f x‖ ∂cubeMeasure d := by
      apply norm_integral_le_of_norm_le
      · exact (MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) (Lp.memLp f)).norm
      · exact Filter.Eventually.of_forall fun x => norm_indicator_le_norm_self _ _
    _ ≤ _ := integral_norm_le_L2_norm f

lemma primitiveRepresentative_memLp (f : Lp ℝ 2 (cubeMeasure d)) :
    MemLp (primitiveRepresentative f) 2 (cubeMeasure d) :=
  MemLp.of_bound (primitiveRepresentative_stronglyMeasurable f).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (primitiveRepresentative_norm_le f))

def primitiveL2Value (f : Lp ℝ 2 (cubeMeasure d)) : Lp ℝ 2 (cubeMeasure d) :=
  (primitiveRepresentative_memLp f).toLp (primitiveRepresentative f)

lemma primitiveL2Value_ae (f : Lp ℝ 2 (cubeMeasure d)) :
    primitiveL2Value f =ᵐ[cubeMeasure d] primitiveRepresentative f :=
  MemLp.coeFn_toLp (primitiveRepresentative_memLp f)

/-- The continuous-linear output represents the manuscript's actual
anchored primitive almost everywhere in the cube variable. -/
lemma primitiveL2Value_ae_boxPrimitive (f : Lp ℝ 2 (cubeMeasure d)) :
    primitiveL2Value f =ᵐ[cubeMeasure d] Tusnady.boxPrimitive f := by
  filter_upwards [primitiveL2Value_ae f,cubeMeasure_ae_UnitCube d] with p hp hcube
  rw [hp, primitiveRepresentative, boxPrimitive_eq_integral_cubeMeasure f p hcube]

lemma primitiveL2Value_norm_le (f : Lp ℝ 2 (cubeMeasure d)) : ‖primitiveL2Value f‖ ≤ ‖f‖ := by
  have hn := Lp.norm_le_of_ae_bound (norm_nonneg f) (f := primitiveL2Value f) (by
    filter_upwards [primitiveL2Value_ae f] with p hp
    rw [hp]
    exact primitiveRepresentative_norm_le f p)
  simpa [measureUnivNNReal, measure_univ] using hn

end Tusnady.Haar

namespace Tusnady.Haar
open MeasureTheory Set
variable {d : ℕ}

lemma primitiveRepresentative_add (f g : Lp ℝ 2 (cubeMeasure d)) (p : Tusnady.Point d) :
    primitiveRepresentative (f+g) p = primitiveRepresentative f p+primitiveRepresentative g p := by
  unfold primitiveRepresentative
  rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add f g))]
  exact integral_add
    ((MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) (Lp.memLp f)).restrict)
    ((MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) (Lp.memLp g)).restrict)

lemma primitiveRepresentative_smul (c : ℝ) (f : Lp ℝ 2 (cubeMeasure d)) (p : Tusnady.Point d) :
    primitiveRepresentative (c • f) p = c*primitiveRepresentative f p := by
  unfold primitiveRepresentative
  rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c f))]
  exact integral_const_mul c f

/-- The actual anchored primitive on the whole cube L² space. -/
def primitiveLinearMap (d : ℕ) : Lp ℝ 2 (cubeMeasure d) →ₗ[ℝ] Lp ℝ 2 (cubeMeasure d) where
  toFun := primitiveL2Value
  map_add' f g := by
    apply Lp.ext
    filter_upwards [primitiveL2Value_ae (f+g), primitiveL2Value_ae f, primitiveL2Value_ae g,
      Lp.coeFn_add (primitiveL2Value f) (primitiveL2Value g)] with p hfg hf hg hadd
    rw [hfg, hadd]
    simpa only [Pi.add_apply, hf, hg] using primitiveRepresentative_add f g p
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [primitiveL2Value_ae (c • f), primitiveL2Value_ae f,
      Lp.coeFn_smul c (primitiveL2Value f)] with p hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul]
    simpa only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hf] using primitiveRepresentative_smul c f p

def primitiveCLM (d : ℕ) : Lp ℝ 2 (cubeMeasure d) →L[ℝ] Lp ℝ 2 (cubeMeasure d) :=
  (primitiveLinearMap d).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using primitiveL2Value_norm_le f)

theorem primitiveCLM_ae (f : Lp ℝ 2 (cubeMeasure d)) :
    primitiveCLM d f =ᵐ[cubeMeasure d] Tusnady.boxPrimitive f := primitiveL2Value_ae_boxPrimitive f

/-- Dimension-independent contraction bound; no finite Haar cap is required. -/
theorem primitiveCLM_norm_le (d : ℕ) : ‖primitiveCLM d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem primitiveCLM_apply_norm_le (f : Lp ℝ 2 (cubeMeasure d)) : ‖primitiveCLM d f‖ ≤ ‖f‖ :=
  primitiveL2Value_norm_le f

/-- Exact connection between the continuous-linear operator norm and the
actual integrated squared primitive appearing in the remainder estimate. -/
theorem primitiveCLM_norm_sq (f : Lp ℝ 2 (cubeMeasure d)) :
    ‖primitiveCLM d f‖^2 = ∫ p, Tusnady.boxPrimitive f p^2 ∂cubeMeasure d := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [primitiveCLM_ae f] with p hp
  simp only [hp, RCLike.inner_apply', conj_trivial, sq]

end Tusnady.Haar

namespace Tusnady.Haar
open MeasureTheory
variable {d : ℕ}

/-- The already constructed actual low and high projections, now exposed
as continuous-linear operators for composition with J. -/
def lowProjectionCLM (d H h : ℕ) : Lp ℝ 2 (cubeMeasure d) →L[ℝ] Lp ℝ 2 (cubeMeasure d) :=
  (spanFor (lowCrossLabels d H h)).starProjection

def highProjectionCLM (d H h : ℕ) : Lp ℝ 2 (cubeMeasure d) →L[ℝ] Lp ℝ 2 (cubeMeasure d) :=
  ContinuousLinearMap.id ℝ _ - lowProjectionCLM d H h

@[simp] theorem lowProjectionCLM_apply (H h : ℕ) (f : Lp ℝ 2 (cubeMeasure d)) :
    lowProjectionCLM d H h f = lowProjection d H h f := rfl

@[simp] theorem highProjectionCLM_apply (H h : ℕ) (f : Lp ℝ 2 (cubeMeasure d)) :
    highProjectionCLM d H h f = highProjection d H h f := rfl

theorem highProjectionCLM_norm_le (d H h : ℕ) : ‖highProjectionCLM d H h‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [one_mul, highProjectionCLM_apply] using highProjection_norm_le h f

/-- The exact operator J*Φ from the cubic remainder estimate. -/
def primitiveHighCLM (d H h : ℕ) : Lp ℝ 2 (cubeMeasure d) →L[ℝ] Lp ℝ 2 (cubeMeasure d) :=
  (primitiveCLM d).comp (highProjectionCLM d H h)

theorem primitiveHighCLM_norm_le (d H h : ℕ) : ‖primitiveHighCLM d H h‖ ≤ 1 := by
  calc
    _ ≤ ‖primitiveCLM d‖*‖highProjectionCLM d H h‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*1 := mul_le_mul (primitiveCLM_norm_le d) (highProjectionCLM_norm_le d H h)
      (norm_nonneg _) (by norm_num)
    _ = 1 := one_mul 1

theorem primitiveHighCLM_norm_sq (H h : ℕ) (f : Lp ℝ 2 (cubeMeasure d)) :
    ‖primitiveHighCLM d H h f‖^2 =
      ∫ p, Tusnady.boxPrimitive (highProjection d H h f) p^2 ∂cubeMeasure d :=
  primitiveCLM_norm_sq (highProjection d H h f)

end Tusnady.Haar
