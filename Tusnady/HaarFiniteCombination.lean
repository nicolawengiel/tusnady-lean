import Tusnady.HaarLowCross
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite high-projection and primitive sums

The exact high-level filter is applied to actual finite tensor combinations.
The resulting anchored primitive is a genuine finite sum of the already
proved coordinate primitives. Cauchy--Schwarz is integrated with explicit
square-integrability, as needed in the cell-location estimate.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open scoped BigOperators

variable {α : Type*}

def combinationL2 {d H : ℕ} (s : Finset α) (c : α → ℝ) (label : α → TensorLabel d H) :
    Lp ℝ 2 (cubeMeasure d) := ∑ a ∈ s, c a • tensorL2 (label a)

def combinationFunction {d H : ℕ} (s : Finset α) (c : α → ℝ) (label : α → TensorLabel d H)
    (x : Fin d → ℝ) : ℝ := ∑ a ∈ s, c a * normalizedTensorValue (label a) x

theorem combination_ae {d H : ℕ} (s : Finset α) (c : α → ℝ) (label : α → TensorLabel d H) :
    combinationL2 s c label =ᵐ[cubeMeasure d] combinationFunction s c label := by
  apply finite_sum_ae s (fun a => c a • tensorL2 (label a))
    (fun a x => c a * normalizedTensorValue (label a) x)
  intro a _
  filter_upwards [Lp.coeFn_smul (c a) (tensorL2 (label a)), tensorL2_ae (label a)] with x hs hb
  exact hs.trans (congrArg (fun y => c a*y) hb)

lemma highProjection_combination_linear {d H : ℕ} (h : ℕ) (s : Finset α)
    (c : α → ℝ) (label : α → TensorLabel d H) :
    highProjection d H h (combinationL2 s c label) =
      ∑ a ∈ s, c a • highProjection d H h (tensorL2 (label a)) := by
  unfold highProjection lowProjection projectionFor combinationL2
  simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
    smul_sub, Finset.sum_sub_distrib]

/-- Explicit retained coefficients: the filter is the proved Haar level,
not an additional retained-component hypothesis. -/
def retainedCoefficient {d H : ℕ} (h : ℕ) (c : α → ℝ) (label : α → TensorLabel d H) (a : α) : ℝ :=
  if (h:ℤ) ≤ tensorLevel (label a) then c a else 0

/-- Exact high-projection filtering of an actual finite tensor combination. -/
theorem highProjection_combination {d H : ℕ} (h : ℕ) (s : Finset α)
    (c : α → ℝ) (label : α → TensorLabel d H) :
    highProjection d H h (combinationL2 s c label) =
      combinationL2 s (retainedCoefficient h c label) label := by
  classical
  rw [highProjection_combination_linear]
  unfold combinationL2
  apply Finset.sum_congr rfl
  intro a _
  rw [highProjection_tensorL2]
  unfold retainedCoefficient
  by_cases hlevel : (h:ℤ) ≤ tensorLevel (label a) <;> simp [hlevel]

theorem highProjection_combination_ae {d H : ℕ} (h : ℕ) (s : Finset α)
    (c : α → ℝ) (label : α → TensorLabel d H) :
    highProjection d H h (combinationL2 s c label) =ᵐ[cubeMeasure d]
      combinationFunction s (retainedCoefficient h c label) label := by
  rw [highProjection_combination]
  exact combination_ae s _ label

/-- Each concrete normalized basis tensor is integrable on every actual
upper box in the unit cube. -/
lemma normalizedTensor_integrable_upperBox {d H : ℕ} (label : TensorLabel d H)
    (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    IntegrableOn (normalizedTensorValue label) (Tusnady.upperBox p) := by
  change Integrable (normalizedTensorValue label)
    ((volume : Measure (Tusnady.Point d)).restrict (Tusnady.upperBox p))
  rw [← cubeMeasure_restrict_upperBox p hp]
  exact (MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) (normalizedTensorValue_memLp label)).integrableOn

/-- Exact primitive of the filtered L² combination, at every point of the
unit cube. Every finite-sum interchange has an integrability proof. -/
theorem boxPrimitive_highProjection_combination {d H : ℕ} (h : ℕ) (s : Finset α)
    (c : α → ℝ) (label : α → TensorLabel d H) (p : Tusnady.Point d)
    (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive (highProjection d H h (combinationL2 s c label)) p =
      ∑ a ∈ s, retainedCoefficient h c label a * normalizedTensorPrimitiveValue (label a) p := by
  rw [boxPrimitive_congr_cube_ae _ _ (highProjection_combination_ae h s c label) p hp]
  unfold combinationFunction
  rw [Tusnady.boxPrimitive_sum s _ p]
  · apply Finset.sum_congr rfl
    intro a _
    rw [Tusnady.boxPrimitive_const_mul,
      boxPrimitive_normalizedTensorValue (label a) p (fun k => (hp k).2)]
  · intro a _
    exact (normalizedTensor_integrable_upperBox (label a) p hp).const_mul _

/-- Integrated finite Cauchy--Schwarz for actual functions. The MemLp
premises are local analytic inputs, not candidate-wide assumptions. -/
theorem integral_sum_sq_le_card_sum {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset α) (F : α → X → ℝ) (hF : ∀ a ∈ s, MemLp (F a) 2 μ) :
    (∫ x, (∑ a ∈ s, F a x)^2 ∂μ) ≤ (s.card:ℝ) * ∑ a ∈ s, ∫ x, F a x^2 ∂μ := by
  have hsum := memLp_finset_sum s hF
  have hint : Integrable (fun x => (∑ a ∈ s, F a x)^2) μ := hsum.integrable_sq
  have hsquares : ∀ a ∈ s, Integrable (fun x => F a x^2) μ := fun a ha => (hF a ha).integrable_sq
  have hright : Integrable (fun x => (s.card:ℝ)*∑ a ∈ s, F a x^2) μ :=
    (integrable_finset_sum s hsquares).const_mul _
  calc
    (∫ x, (∑ a ∈ s, F a x)^2 ∂μ) ≤ ∫ x, (s.card:ℝ)*∑ a ∈ s, F a x^2 ∂μ := by
      apply integral_mono hint hright
      intro x
      exact sq_sum_le_card_mul_sum_sq
    _ = _ := by rw [integral_const_mul, integral_finset_sum s hsquares]

/-- Uniform component norm control gives the square of the number of
components, exactly the Cauchy--Schwarz step in Manuscript Lemma 4.3. -/
theorem integral_sum_sq_le_card_sq {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Finset α) (F : α → X → ℝ) (hF : ∀ a ∈ s, MemLp (F a) 2 μ)
    (B : ℝ) (hB : ∀ a ∈ s, (∫ x, F a x^2 ∂μ) ≤ B) :
    (∫ x, (∑ a ∈ s, F a x)^2 ∂μ) ≤ (s.card:ℝ)^2*B := by
  calc
    _ ≤ (s.card:ℝ)*∑ a ∈ s, ∫ x, F a x^2 ∂μ := integral_sum_sq_le_card_sum μ s F hF
    _ ≤ (s.card:ℝ)*∑ _a ∈ s, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hB) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Tusnady.Haar
