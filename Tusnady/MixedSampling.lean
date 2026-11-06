import Tusnady.Literature
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Linarith

/-!
# Mixed sampling: density normalization and the additional square-root function

These are proved portions of Manuscript Lemma 5.3. A positive density `ρ`
normalizes an orthonormal system before the literature sampling theorem is
applied. The resulting equal-weight sample is converted back to weights
`1/(m ρ(Pᵢ))`. Adjoining the *single* function `sqrt w` then transfers an
integrated mean-square error bound to the same sample.

No global axiom is introduced here. The named LT22 literature hypothesis is
applied explicitly to a given basis and its density; the universal sampling
constants are retained. The concrete Christoffel density construction and
its estimates for the manuscript space, dimension estimates, and perturbation
to distinct points still need their own proofs.
-/

set_option autoImplicit false

namespace Tusnady.MixedSampling

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section

variable {α : Type*}

/-- The function used after the density change. -/
def normalize (ρ : α → ℝ≥0) (f : α → ℝ) : α → ℝ :=
  fun x => f x / Real.sqrt (ρ x)

/-- Weights when returning a sample from density `ρ` to the original measure. -/
def weight {m : ℕ} (ρ : α → ℝ≥0) (P : Fin m → α) (i : Fin m) : ℝ :=
  1 / ((m : ℝ) * (ρ (P i) : ℝ))

/-- Exact cancellation of the density in a normalized squared value. -/
theorem density_mul_normalize_sq (ρ : α → ℝ≥0) (f : α → ℝ)
    (hρ : ∀ x, 0 < ρ x) (x : α) :
    (ρ x : ℝ) * normalize ρ f x ^ 2 = f x ^ 2 := by
  have hp : (0 : ℝ) < ρ x := hρ x
  unfold normalize
  rw [div_pow, Real.sq_sqrt hp.le]
  exact mul_div_cancel₀ (f x ^ 2) (ne_of_gt hp)

/-- Exact squared-integral identity for an actual `withDensity` measure.
It is proved using mathlib's Bochner change-of-density theorem. -/
theorem integral_normalize_sq [MeasurableSpace α] (μ : Measure α)
    (ρ : α → ℝ≥0) (f : α → ℝ) (hρmeas : Measurable ρ)
    (hρ : ∀ x, 0 < ρ x) :
    (∫ x, normalize ρ f x ^ 2 ∂μ.withDensity (fun x => (ρ x : ℝ≥0∞))) =
      ∫ x, f x ^ 2 ∂μ := by
  rw [integral_withDensity_eq_integral_smul hρmeas]
  apply integral_congr_ae
  filter_upwards [] with x
  change (ρ x : ℝ) * normalize ρ f x ^ 2 = f x ^ 2
  exact density_mul_normalize_sq ρ f hρ x

/-- Density cancellation also preserves mixed moments, as required for
orthogonality of the normalized basis. -/
theorem density_mul_normalize_mul (ρ : α → ℝ≥0) (f g : α → ℝ)
    (hρ : ∀ x, 0 < ρ x) (x : α) :
    (ρ x : ℝ) * (normalize ρ f x * normalize ρ g x) = f x * g x := by
  have hp : (0 : ℝ) < ρ x := hρ x
  have hs : Real.sqrt (ρ x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hsq := Real.sq_sqrt hp.le
  unfold normalize
  field_simp
  rw [hsq]
  ring

/-- The actual density change preserves all basis mixed integrals. -/
theorem integral_normalize_mul [MeasurableSpace α] (μ : Measure α)
    (ρ : α → ℝ≥0) (f g : α → ℝ) (hρmeas : Measurable ρ)
    (hρ : ∀ x, 0 < ρ x) :
    (∫ x, normalize ρ f x * normalize ρ g x
      ∂μ.withDensity (fun x => (ρ x : ℝ≥0∞))) = ∫ x, f x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_smul hρmeas]
  apply integral_congr_ae
  filter_upwards [] with x
  change (ρ x : ℝ) * (normalize ρ f x * normalize ρ g x) = f x * g x
  exact density_mul_normalize_mul ρ f g hρ x

/-- Defining the density as the average squared basis evaluation gives the
pointwise Condition E identity with parameter one. The density identity is
an explicit definition equation, rather than a new estimate. -/
theorem normalized_conditionE {D : ℕ} (hD : 0 < D)
    (φ : Fin D → α → ℝ) (ρ : α → ℝ≥0) (hρ : ∀ x, 0 < ρ x)
    (hdensity : ∀ x, (ρ x : ℝ) = (1 / (D : ℝ)) * ∑ k, φ k x ^ 2) (x : α) :
    (∑ k, normalize ρ (φ k) x ^ 2) = (D : ℝ) := by
  have hp : (0 : ℝ) < ρ x := hρ x
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  simp only [normalize, div_pow, Real.sq_sqrt hp.le]
  rw [← Finset.sum_div]
  apply (div_eq_iff (ne_of_gt hp)).2
  have hd := hdensity x
  field_simp at hd
  nlinarith

/-- A positive integrable density of integral one defines a probability
measure. This closes the measure normalization step once its Christoffel
formula has been established. -/
theorem density_isProbabilityMeasure [MeasurableSpace α] (μ : Measure α)
    (ρ : α → ℝ≥0) (hρint : Integrable (fun x => (ρ x : ℝ)) μ)
    (hρone : (∫ x, (ρ x : ℝ) ∂μ) = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => (ρ x : ℝ≥0∞))) := by
  apply isProbabilityMeasure_iff.mpr
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_coe_eq_integral ρ hρint, hρone]
  norm_num

/-- The finite sum transforms by exactly the same weights as the integral. -/
theorem weighted_square_sum_eq {m : ℕ} (hm : 0 < m)
    (ρ : α → ℝ≥0) (P : Fin m → α) (f : α → ℝ)
    (hρ : ∀ x, 0 < ρ x) :
    (∑ i, weight ρ P i * f (P i) ^ 2) =
      (1 / (m : ℝ)) * ∑ i, normalize ρ f (P i) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hp : (0 : ℝ) < ρ (P i) := hρ (P i)
  unfold weight normalize
  rw [div_pow, Real.sq_sqrt hp.le]
  field_simp

/-- Every returned quadrature weight is strictly positive. -/
theorem weight_pos {m : ℕ} (hm : 0 < m) (ρ : α → ℝ≥0) (P : Fin m → α)
    (hρ : ∀ x, 0 < ρ x) (i : Fin m) : 0 < weight ρ P i := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : (0 : ℝ) < ρ (P i) := hρ (P i)
  exact one_div_pos.mpr (mul_pos hm' hp)

/-- A uniform positive density bound gives the required `O(1/m)` weights. -/
theorem weight_le {m : ℕ} (hm : 0 < m) (ρ : α → ℝ≥0) (P : Fin m → α)
    (c : ℝ) (hc : 0 < c) (hρ : ∀ x, c ≤ (ρ x : ℝ)) (i : Fin m) :
    weight ρ P i ≤ 1 / ((m : ℝ) * c) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  exact one_div_le_one_div_of_le (mul_pos hm' hc)
    (mul_le_mul_of_nonneg_left (hρ (P i)) hm'.le)

/-- Transfer both norm inequalities for one function, preserving the constants.
The input is exactly the conclusion of the equal-weight sampling theorem
for its normalized function; this lemma proves the change back to `μ`. -/
theorem transfer_function [MeasurableSpace α] (μ : Measure α)
    {m : ℕ} (hm : 0 < m) (ρ : α → ℝ≥0) (P : Fin m → α)
    (hρmeas : Measurable ρ) (hρ : ∀ x, 0 < ρ x)
    (f : α → ℝ) (c C : ℝ)
    (hsample :
      c * (∫ x, normalize ρ f x ^ 2 ∂μ.withDensity (fun x => (ρ x : ℝ≥0∞))) ≤
        (1 / (m : ℝ)) * ∑ i, normalize ρ f (P i) ^ 2 ∧
      (1 / (m : ℝ)) * (∑ i, normalize ρ f (P i) ^ 2) ≤
        C * (∫ x, normalize ρ f x ^ 2 ∂μ.withDensity (fun x => (ρ x : ℝ≥0∞)))) :
    c * (∫ x, f x ^ 2 ∂μ) ≤ ∑ i, weight ρ P i * f (P i) ^ 2 ∧
      (∑ i, weight ρ P i * f (P i) ^ 2) ≤ C * (∫ x, f x ^ 2 ∂μ) := by
  rw [integral_normalize_sq μ ρ f hρmeas hρ] at hsample
  rw [weighted_square_sum_eq hm ρ P f hρ]
  exact hsample

/-- Normalization preserves pairwise product integrability under the
actual density measure, rather than merely preserving formal integrals. -/
theorem normalize_mul_integrable [MeasurableSpace α] (μ : Measure α)
    (ρ : α → ℝ≥0) (f g : α → ℝ) (hρmeas : Measurable ρ)
    (hρ : ∀ x, 0 < ρ x) (hfg : Integrable (fun x => f x * g x) μ) :
    Integrable (fun x => normalize ρ f x * normalize ρ g x)
      (μ.withDensity (fun x => (ρ x : ℝ≥0∞))) := by
  apply (integrable_withDensity_iff_integrable_smul hρmeas).2
  change Integrable (fun x => (ρ x : ℝ) * (normalize ρ f x * normalize ρ g x)) μ
  simpa only [density_mul_normalize_mul ρ f g hρ] using hfg

/-- Finite linear combinations commute with density normalization. -/
theorem normalize_sum {D : ℕ} (ρ : α → ℝ≥0) (φ : Fin D → α → ℝ)
    (a : Fin D → ℝ) (x : α) :
    normalize ρ (fun x => ∑ i, a i * φ i x) x =
      ∑ i, a i * normalize ρ (φ i) x := by
  simp only [normalize, Finset.sum_div, mul_div_assoc]

/-- The Christoffel density is integrable as a finite average of the
integrable diagonal basis products. -/
theorem christoffel_density_integrable [MeasurableSpace α] (μ : Measure α)
    {D : ℕ} (φ : Fin D → α → ℝ) (ρ : α → ℝ≥0)
    (hφint : ∀ i j, Integrable (fun x => φ i x * φ j x) μ)
    (hdensity : ∀ x, (ρ x : ℝ) = (1 / (D : ℝ)) * ∑ i, φ i x ^ 2) :
    Integrable (fun x => (ρ x : ℝ)) μ := by
  have hsquares : ∀ i : Fin D, Integrable (fun x => φ i x ^ 2) μ := by
    intro i
    simpa only [pow_two] using hφint i i
  have hsum := integrable_finset_sum Finset.univ (fun i _ => hsquares i)
  have hnormalized := hsum.const_mul (1 / (D : ℝ))
  apply hnormalized.congr
  filter_upwards [] with x
  exact (hdensity x).symm

/-- An orthonormal basis makes the Christoffel density integrate to one;
the normalization is proved, rather than added as a separate assumption. -/
theorem integral_christoffel_density [MeasurableSpace α] (μ : Measure α)
    {D : ℕ} (hD : 0 < D) (φ : Fin D → α → ℝ) (ρ : α → ℝ≥0)
    (hφint : ∀ i j, Integrable (fun x => φ i x * φ j x) μ)
    (hφorth : ∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0)
    (hdensity : ∀ x, (ρ x : ℝ) = (1 / (D : ℝ)) * ∑ i, φ i x ^ 2) :
    (∫ x, (ρ x : ℝ) ∂μ) = 1 := by
  have hsquares : ∀ i : Fin D, Integrable (fun x => φ i x ^ 2) μ := by
    intro i
    simpa only [pow_two] using hφint i i
  have hdiag : ∀ i : Fin D, (∫ x, φ i x ^ 2 ∂μ) = 1 := by
    intro i
    simpa only [pow_two, if_pos rfl, ite_true] using hφorth i i
  have hρfun : (fun x => (ρ x : ℝ)) =
      (fun x => (1 / (D : ℝ)) * ∑ i, φ i x ^ 2) := funext hdensity
  rw [hρfun, integral_const_mul, integral_finset_sum Finset.univ (fun i _ => hsquares i)]
  simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  exact one_div_mul_cancel hD'

/-- The LT22 assumption is applied to the normalized basis. The output
constants are chosen before all dimensions, domains, measures and bases,
so their universality is retained by this formal application. -/
theorem weighted_sampling_from_literature (hLT : Tusnady.Literature.Sampling) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∀ (ambient D : ℕ), 0 < D →
      ∀ Ω : Set (Tusnady.Literature.Vector ambient), Ω.Nonempty →
      ∀ (μ : Measure Ω) (φ : Fin D → Ω → ℝ) (ρ : Ω → ℝ≥0),
        (∀ i, Measurable (φ i)) →
        (∀ i j, Integrable (fun x => φ i x * φ j x) μ) →
        (∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0) →
        Measurable ρ → (∀ x, 0 < ρ x) →
        (∀ x, (ρ x : ℝ) = (1 / (D : ℝ)) * ∑ i, φ i x ^ 2) →
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C₁ * (D : ℝ) ∧
          ∃ P : Fin m → Ω, ∀ a : Fin D → ℝ,
            C₂ * (∫ x, (∑ i, a i * φ i x) ^ 2 ∂μ) ≤
              ∑ j, weight ρ P j * (∑ i, a i * φ i (P j)) ^ 2 ∧
            (∑ j, weight ρ P j * (∑ i, a i * φ i (P j)) ^ 2) ≤
              C₃ * (∫ x, (∑ i, a i * φ i x) ^ 2 ∂μ) := by
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hsample⟩ := hLT
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, ?_⟩
  intro ambient D hD Ω hΩ μ φ ρ hφmeas hφint hφorth hρmeas hρ hdensity
  let ν := μ.withDensity (fun x => (ρ x : ℝ≥0∞))
  have hν : IsProbabilityMeasure ν := density_isProbabilityMeasure μ ρ
    (christoffel_density_integrable μ φ ρ hφint hdensity)
    (integral_christoffel_density μ hD φ ρ hφint hφorth hdensity)
  have humeas : ∀ i, Measurable (normalize ρ (φ i)) := by
    intro i
    exact (hφmeas i).div hρmeas.coe_nnreal_real.sqrt
  have huint : ∀ i j, Integrable
      (fun x => normalize ρ (φ i) x * normalize ρ (φ j) x) ν := by
    intro i j
    exact normalize_mul_integrable μ ρ (φ i) (φ j) hρmeas hρ (hφint i j)
  have huorth : ∀ i j,
      (∫ x, normalize ρ (φ i) x * normalize ρ (φ j) x ∂ν) =
        if i = j then 1 else 0 := by
    intro i j
    rw [integral_normalize_mul μ ρ (φ i) (φ j) hρmeas hρ]
    exact hφorth i j
  have hucond : ∀ x, (∑ i, |normalize ρ (φ i) x| ^ 2) ≤ (D : ℝ) := by
    intro x
    simp only [sq_abs]
    rw [normalized_conditionE hD φ ρ hρ hdensity x]
  obtain ⟨m, hm, hmcard, P, hP⟩ :=
    hsample ambient D hD Ω hΩ ν hν (fun i => normalize ρ (φ i)) humeas huint huorth hucond
  refine ⟨m, hm, hmcard, P, ?_⟩
  intro a
  have hPa := hP a
  simp only [sq_abs, ← normalize_sum] at hPa
  exact transfer_function μ hm ρ P hρmeas hρ (fun x => ∑ i, a i * φ i x) C₂ C₃ hPa

/-- Only one extra function is adjoined to the norm-sampling space. -/
def enlargedSpace (V : Submodule ℝ (α → ℝ)) (w : α → ℝ) :
    Submodule ℝ (α → ℝ) :=
  V ⊔ Submodule.span ℝ {fun x => Real.sqrt (w x)}

/-- Every original sampling function is in the enlarged space. -/
theorem mem_enlargedSpace_of_mem (V : Submodule ℝ (α → ℝ)) (w : α → ℝ)
    (f : α → ℝ) (hf : f ∈ V) : f ∈ enlargedSpace V w :=
  (show V ≤ enlargedSpace V w from le_sup_left) hf

/-- The scalar witness is in the same enlarged space. -/
theorem sqrt_mem_enlargedSpace (V : Submodule ℝ (α → ℝ)) (w : α → ℝ) :
    (fun x => Real.sqrt (w x)) ∈ enlargedSpace V w := by
  apply (show Submodule.span ℝ {fun x => Real.sqrt (w x)} ≤ enlargedSpace V w from le_sup_right)
  exact Submodule.subset_span (Set.mem_singleton _)

/-- Sampling the square root controls the nonnegative scalar error directly. -/
theorem sqrt_control [MeasurableSpace α] (μ : Measure α)
    {m : ℕ} (a : Fin m → ℝ) (P : Fin m → α) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (C : ℝ)
    (hsample : (∑ i, a i * Real.sqrt (w (P i)) ^ 2) ≤
      C * (∫ x, Real.sqrt (w x) ^ 2 ∂μ)) :
    (∑ i, a i * w (P i)) ≤ C * (∫ x, w x ∂μ) := by
  simpa only [Real.sq_sqrt (hw _)] using hsample

/-- Simultaneous norm sampling on `V` and scalar sampling of `w` follow
from norm sampling on `V + span{sqrt w}`, after the actual density change.
This theorem proves the transfer, but does not assert the existence or
pairwise distinctness of the sample points. -/
theorem mixed_transfer [MeasurableSpace α] (μ : Measure α)
    {m : ℕ} (hm : 0 < m) (V : Submodule ℝ (α → ℝ)) (w : α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (ρ : α → ℝ≥0) (P : Fin m → α)
    (hρmeas : Measurable ρ) (hρ : ∀ x, 0 < ρ x) (c C : ℝ)
    (hsample : ∀ f ∈ enlargedSpace V w,
      c * (∫ x, normalize ρ f x ^ 2 ∂μ.withDensity (fun x => (ρ x : ℝ≥0∞))) ≤
        (1 / (m : ℝ)) * ∑ i, normalize ρ f (P i) ^ 2 ∧
      (1 / (m : ℝ)) * (∑ i, normalize ρ f (P i) ^ 2) ≤
        C * (∫ x, normalize ρ f x ^ 2 ∂μ.withDensity (fun x => (ρ x : ℝ≥0∞)))) :
    (∀ f ∈ V,
      c * (∫ x, f x ^ 2 ∂μ) ≤ ∑ i, weight ρ P i * f (P i) ^ 2 ∧
      (∑ i, weight ρ P i * f (P i) ^ 2) ≤ C * (∫ x, f x ^ 2 ∂μ)) ∧
    (∑ i, weight ρ P i * w (P i)) ≤ C * (∫ x, w x ∂μ) := by
  constructor
  · intro f hf
    exact transfer_function μ hm ρ P hρmeas hρ f c C
      (hsample f (mem_enlargedSpace_of_mem V w f hf))
  · apply sqrt_control μ (weight ρ P) P w hw C
    exact (transfer_function μ hm ρ P hρmeas hρ (fun x => Real.sqrt (w x)) c C
      (hsample _ (sqrt_mem_enlargedSpace V w))).2

/-- Application of the named literature sampling hypothesis to a basis
spanning the enlarged space. Both the original norm inequality and the
scalar error inequality are produced on the same weighted point list.

The hypotheses describe generic input data: a concrete orthonormal finite
basis, its Christoffel density, and its spanning property. Constructing those
data for the manuscript's `V_H` remains separate, as does making the returned
points distinct. Universality of the three constants is recorded in the
stronger theorem `weighted_sampling_from_literature` above. -/
theorem mixed_sampling_from_literature
    (hLT : Tusnady.Literature.Sampling) (ambient D : ℕ) (hD : 0 < D)
    (Ω : Set (Tusnady.Literature.Vector ambient)) (hΩ : Ω.Nonempty)
    (μ : Measure Ω) (φ : Fin D → Ω → ℝ) (ρ : Ω → ℝ≥0)
    (hφmeas : ∀ i, Measurable (φ i))
    (hφint : ∀ i j, Integrable (fun x => φ i x * φ j x) μ)
    (hφorth : ∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0)
    (hρmeas : Measurable ρ)
    (hdensity : ∀ x, (ρ x : ℝ) = (1 / (D : ℝ)) * ∑ i, φ i x ^ 2)
    (lower : ℝ) (hlower : 0 < lower) (hρlower : ∀ x, lower ≤ (ρ x : ℝ))
    (V : Submodule ℝ (Ω → ℝ)) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hspan : ∀ f ∈ enlargedSpace V w,
      ∃ a : Fin D → ℝ, (fun x => ∑ i, a i * φ i x) = f) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C₁ * (D : ℝ) ∧
        ∃ P : Fin m → Ω,
          (∀ i, 0 < weight ρ P i ∧ weight ρ P i ≤ 1 / ((m : ℝ) * lower)) ∧
          (∀ f ∈ V,
            C₂ * (∫ x, f x ^ 2 ∂μ) ≤ ∑ i, weight ρ P i * f (P i) ^ 2 ∧
            (∑ i, weight ρ P i * f (P i) ^ 2) ≤ C₃ * (∫ x, f x ^ 2 ∂μ)) ∧
          (∑ i, weight ρ P i * w (P i)) ≤ C₃ * (∫ x, w x ∂μ) := by
  have hρ : ∀ x, 0 < ρ x := by
    intro x
    exact_mod_cast (lt_of_lt_of_le hlower (hρlower x))
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hsample⟩ :=
    weighted_sampling_from_literature hLT
  obtain ⟨m, hm, hmcard, P, hP⟩ :=
    hsample ambient D hD Ω hΩ μ φ ρ hφmeas hφint hφorth hρmeas hρ hdensity
  have hU : ∀ f ∈ enlargedSpace V w,
      C₂ * (∫ x, f x ^ 2 ∂μ) ≤ ∑ i, weight ρ P i * f (P i) ^ 2 ∧
      (∑ i, weight ρ P i * f (P i) ^ 2) ≤ C₃ * (∫ x, f x ^ 2 ∂μ) := by
    intro f hf
    obtain ⟨a, hfa⟩ := hspan f hf
    subst f
    exact hP a
  refine ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, m, hm, hmcard, P, ?_, ?_, ?_⟩
  · intro i
    exact ⟨weight_pos hm ρ P hρ i, weight_le hm ρ P lower hlower hρlower i⟩
  · intro f hf
    exact hU f (mem_enlargedSpace_of_mem V w f hf)
  · exact sqrt_control μ (weight ρ P) P w hw C₃
      (hU _ (sqrt_mem_enlargedSpace V w)).2

end

end Tusnady.MixedSampling
