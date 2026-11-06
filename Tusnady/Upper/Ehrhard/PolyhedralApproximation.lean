import Tusnady.Upper.Ehrhard.AffineSoftMinimum
import Tusnady.Upper.Ehrhard.Quantile

/-!
# Smooth, concave, boundary-preserving approximation of finite halfspaces

For affine slacks `b i + inner (v i) x`, the smooth concave function is
`n - log (∑ i, exp (-n² * slack i x))`.  The additive `n` diverges more slowly
than `n²`.  Consequently its Gaussian CDF tends to the indicator of the CLOSED
intersection, including all boundary points.  No Gaussian boundary-null lemma
and no nonzero-normal-vector hypothesis is needed.

All derivative data and global gradient/Hessian bounds are proved explicitly.
The final dominated-convergence lemma works for any actual probability measure
and measurable input map, including a degenerate Gaussian affine map.
-/

namespace OAI
namespace GaussianPropeller.AffineSoftMin

universe uE uι uX
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
open GaussianPropeller.Quantile

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type uι} [Fintype ι] [Nonempty ι]

def slackSet (v : ι → E) (b : ι → ℝ) : Set E := {x | ∀ i, 0 ≤ b i + ⟪v i,x⟫}

noncomputable def approxValue (n : ℕ) (v : ι → E) (b : ι → ℝ) (x : E) : ℝ :=
  (n : ℝ) + value (fun i => (n : ℝ)^2 • v i) (fun i => (n : ℝ)^2 * b i) x

noncomputable def approxGrad (n : ℕ) (v : ι → E) (b : ι → ℝ) (x : E) : E :=
  grad (fun i => (n : ℝ)^2 • v i) (fun i => (n : ℝ)^2 * b i) x

noncomputable def approxHess (n : ℕ) (v : ι → E) (b : ι → ℝ) (x : E) : E →L[ℝ] E :=
  hess (fun i => (n : ℝ)^2 • v i) (fun i => (n : ℝ)^2 * b i) x

theorem approxValue_fderiv (n : ℕ) (v : ι → E) (b : ι → ℝ) (x : E) :
    HasFDerivAt (approxValue n v b) (innerSL ℝ (approxGrad n v b x)) x :=
  (value_fderiv (fun i => (n : ℝ)^2 • v i) (fun i => (n : ℝ)^2 * b i) x).const_add (n : ℝ)

theorem approxGrad_fderiv (n : ℕ) (v : ι → E) (b : ι → ℝ) (x : E) :
    HasFDerivAt (approxGrad n v b) (approxHess n v b x) x :=
  grad_fderiv (fun i => (n : ℝ)^2 • v i) (fun i => (n : ℝ)^2 * b i) x

theorem approxHess_continuous (n : ℕ) (v : ι → E) (b : ι → ℝ) :
    Continuous (approxHess n v b) :=
  continuous_hess (fun i => (n : ℝ)^2 • v i) (fun i => (n : ℝ)^2 * b i)

theorem approxValue_concave (n : ℕ) (v : ι → E) (b : ι → ℝ) :
    ConcaveOn ℝ univ (approxValue n v b) := by
  simpa only [approxValue, Pi.add_apply, add_comm] using!
    (value_concave (fun i => (n : ℝ)^2 • v i) (fun i => (n : ℝ)^2 * b i)).add_const (n : ℝ)

theorem approxGrad_bound (n : ℕ) (v : ι → E) (b : ι → ℝ)
    {L : ℝ} (hL : ∀ i, ‖v i‖ ≤ L) (x : E) :
    ‖approxGrad n v b x‖ ≤ (n : ℝ)^2 * L := by
  apply grad_bound
  intro i
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))] using
    mul_le_mul_of_nonneg_left (hL i) (sq_nonneg (n : ℝ))

theorem approxHess_bound (n : ℕ) (v : ι → E) (b : ι → ℝ)
    {L : ℝ} (hL0 : 0 ≤ L) (hL : ∀ i, ‖v i‖ ≤ L) (x : E) :
    ‖approxHess n v b x‖ ≤ 2 * ((n : ℝ)^2 * L)^2 := by
  apply hess_bound _ _ (mul_nonneg (sq_nonneg _) hL0)
  intro i
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (n : ℝ))] using
    mul_le_mul_of_nonneg_left (hL i) (sq_nonneg (n : ℝ))

theorem approxValue_tendsto_atTop (v : ι → E) (b : ι → ℝ) (x : E)
    (hx : x ∈ slackSet v b) :
    Tendsto (fun n : ℕ => approxValue n v b x) atTop atTop := by
  have hbound (n : ℕ) : (n : ℝ) - Real.log (Fintype.card ι : ℝ) ≤ approxValue n v b x := by
    have h := value_lower_bound (fun i => (n : ℝ)^2 • v i)
      (fun i => (n : ℝ)^2 * b i) x 0 (fun i => by
        simp only [real_inner_smul_left]
        nlinarith [sq_nonneg (n : ℝ), hx i])
    dsimp only [approxValue]
    linarith
  apply tendsto_atTop_mono hbound
  apply tendsto_atTop.2
  intro r
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_ge_atTop (r + Real.log (Fintype.card ι : ℝ)))] with n hn
  linarith

theorem approxValue_tendsto_atBot (v : ι → E) (b : ι → ℝ) (x : E)
    (hx : x ∉ slackSet v b) :
    Tendsto (fun n : ℕ => approxValue n v b x) atTop atBot := by
  simp only [slackSet, mem_setOf_eq, not_forall, not_le] at hx
  obtain ⟨i, hi⟩ := hx
  have hc : Tendsto (fun n : ℕ => 1 + (n : ℝ) * (b i + ⟪v i,x⟫)) atTop atBot := by
    have hb := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const_of_neg hi
    apply tendsto_atBot.2
    intro r
    filter_upwards [hb.eventually (eventually_le_atBot (r - 1))] with n hn
    linarith
  have hp := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_atBot₀ hc
  have hp' : Tendsto (fun n : ℕ => (n : ℝ) + (n : ℝ)^2 * (b i + ⟪v i,x⟫)) atTop atBot := by
    convert hp using 1
    funext n
    ring
  apply tendsto_atBot_mono (fun n => ?_) hp'
  have h := value_le_score (fun j => (n : ℝ)^2 • v j)
    (fun j => (n : ℝ)^2 * b j) x i
  simp only [real_inner_smul_left] at h
  dsimp only [approxValue]
  nlinarith

/-- Pointwise convergence includes every boundary point, even zero normals. -/
theorem cdf_approxValue_limit (v : ι → E) (b : ι → ℝ) (x : E) :
    Tendsto (fun n : ℕ => Φ (approxValue n v b x)) atTop
      (𝓝 ((slackSet v b).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ slackSet v b
  · rw [indicator_of_mem hx]
    exact tendsto_Φ_atTop.comp (approxValue_tendsto_atTop v b x hx)
  · rw [indicator_of_notMem hx]
    exact tendsto_Φ_atBot.comp (approxValue_tendsto_atBot v b x hx)

section Measure

variable [MeasurableSpace E] [BorelSpace E]

omit [Nonempty ι] in
theorem measurableSet_slackSet (v : ι → E) (b : ι → ℝ) : MeasurableSet (slackSet v b) := by
  change MeasurableSet {x : E | ∀ i, 0 ≤ b i + ⟪v i,x⟫}
  have heq : {x : E | ∀ i, 0 ≤ b i + ⟪v i,x⟫} = ⋂ i, {x : E | 0 ≤ b i + ⟪v i,x⟫} := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iInter (fun i => measurableSet_le
    (measurable_const : Measurable (fun _ : E => (0 : ℝ)))
    (show Measurable (fun x : E => b i + ⟪v i,x⟫) by fun_prop))

/-- Dominated convergence under any actual probability measure, including
degenerate Gaussian affine noise. -/
theorem integral_cdf_approxValue_limit {X : Type uX} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (v : ι → E) (b : ι → ℝ)
    (F : X → E) (hF : Measurable F) :
    Tendsto (fun n : ℕ => ∫ z, Φ (approxValue n v b (F z)) ∂μ) atTop
      (𝓝 (μ.real (F ⁻¹' slackSet v b))) := by
  have hc (n : ℕ) : Continuous (approxValue n v b) :=
    continuous_iff_continuousAt.mpr (fun x => (approxValue_fderiv n v b x).continuousAt)
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (bound := fun _ : X => (1 : ℝ))
    (F := fun n : ℕ => fun z : X => Φ (approxValue n v b (F z)))
    (f := fun z : X => (slackSet v b).indicator (fun _ => (1 : ℝ)) (F z))
    (fun n => ((continuous_Φ.comp (hc n)).measurable.comp hF).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_pos (Φ_pos _)]
      exact (Φ_lt_one _).le))
    (ae_of_all _ (fun z => cdf_approxValue_limit v b (F z)))
  convert hlim using 1
  rw [show (fun z : X => (slackSet v b).indicator (fun _ => (1 : ℝ)) (F z)) =
      (F ⁻¹' slackSet v b).indicator (fun _ => (1 : ℝ)) from rfl,
    integral_indicator ((measurableSet_slackSet v b).preimage hF), setIntegral_const]
  simp

end Measure
end GaussianPropeller.AffineSoftMin
end OAI
