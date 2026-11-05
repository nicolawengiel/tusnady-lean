import Tusnady.HaarProjection
import Tusnady.Primitive

/-!
# Actual anchored primitives of the finite tensor Haar functions

The identities use the project's genuine closed-upper-box integral operator.
The squared norm constants are proved by actual product Lebesgue integrals.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators

/-- The product cube measure is supported on the actual half-open unit cube. -/
theorem cubeMeasure_ae_unit (d : ℕ) :
    ∀ᵐ x ∂cubeMeasure d, ∀ k, x k ∈ Ico (0:ℝ) 1 := by
  apply ae_all_iff.mpr
  intro k
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin d => unitMeasure) (i := k))
    (ae_restrict_mem measurableSet_Ico)

/-- Coordinate primitive: constants give 1-p, Haar functions give negative tents. -/
def primitiveValue {H : ℕ} (label : Label H) (p : ℝ) : ℝ :=
  match label with
  | none => 1-p
  | some ⟨a,i⟩ => -tentI a.val i p

/-- Exact squared integral of each coordinate primitive. -/
def primitiveMass {H : ℕ} (label : Label H) : ℝ :=
  match label with
  | none => 1/3
  | some ⟨a,_⟩ => dyadicLength a.val^3/12

lemma integral_value_right {H : ℕ} (label : Label H) (p : ℝ) :
    (∫ x in p..1, value label x) = primitiveValue label p := by
  cases label with
  | none => simp [value, primitiveValue, intervalIntegral.integral_const]
  | some label => exact integral_hI_right_unit label.1.val label.2 p

lemma integral_primitiveValue_sq {H : ℕ} (label : Label H) :
    (∫ p, primitiveValue label p^2 ∂unitMeasure) = primitiveMass label := by
  rw [integral_unitMeasure]
  cases label with
  | none =>
    change (∫ p in (0:ℝ)..1, (1-p)^2) = (1:ℝ)/3
    have hfun : (fun p : ℝ => (1-p)^2) = (fun p => ((-1:ℝ)*p+1)^2) := by funext p; ring
    rw [hfun, integral_affine_sq]
    norm_num
  | some label =>
    have h := integral_unit_haarPrimitive_sq label.1.val label.2
    simpa only [integral_hI_right_unit, primitiveValue, primitiveMass] using h

def normalizedPrimitiveValue {H : ℕ} (label : Label H) (p : ℝ) : ℝ :=
  primitiveValue label p/Real.sqrt (mass label)

lemma integral_normalizedValue_right {H : ℕ} (label : Label H) (p : ℝ) :
    (∫ x in p..1, normalizedValue label x) = normalizedPrimitiveValue label p := by
  unfold normalizedValue normalizedPrimitiveValue
  rw [intervalIntegral.integral_div, integral_value_right]

lemma integral_normalizedPrimitiveValue_sq {H : ℕ} (label : Label H) :
    (∫ p, normalizedPrimitiveValue label p^2 ∂unitMeasure) = primitiveMass label/mass label := by
  unfold normalizedPrimitiveValue
  simp_rw [div_pow, Real.sq_sqrt (mass_pos label).le]
  rw [integral_div, integral_primitiveValue_sq]

/-- The tensor of the explicit coordinate primitives. -/
def tensorPrimitiveValue {d H : ℕ} (label : TensorLabel d H) (p : Fin d → ℝ) : ℝ :=
  ∏ k, primitiveValue (label k) (p k)

def normalizedTensorPrimitiveValue {d H : ℕ} (label : TensorLabel d H) (p : Fin d → ℝ) : ℝ :=
  ∏ k, normalizedPrimitiveValue (label k) (p k)

/-- Exact genuine primitive of every finite tensor Haar function. -/
theorem boxPrimitive_tensorValue {d H : ℕ} (label : TensorLabel d H) (p : Fin d → ℝ)
    (hp : ∀ k, p k ≤ 1) :
    Tusnady.boxPrimitive (tensorValue label) p = tensorPrimitiveValue label p := by
  unfold tensorValue tensorPrimitiveValue
  rw [Tusnady.boxPrimitive_tensor_interval (fun k => value (label k)) p hp]
  simp_rw [integral_value_right]

/-- Exact genuine primitive of the normalized tensor family used by L² projections. -/
theorem boxPrimitive_normalizedTensorValue {d H : ℕ} (label : TensorLabel d H) (p : Fin d → ℝ)
    (hp : ∀ k, p k ≤ 1) :
    Tusnady.boxPrimitive (normalizedTensorValue label) p = normalizedTensorPrimitiveValue label p := by
  unfold normalizedTensorValue normalizedTensorPrimitiveValue
  rw [Tusnady.boxPrimitive_tensor_interval (fun k => normalizedValue (label k)) p hp]
  simp_rw [integral_normalizedValue_right]

/-- Exact product norm of the raw tensor primitive. -/
theorem integral_tensorPrimitiveValue_sq {d H : ℕ} (label : TensorLabel d H) :
    (∫ p, tensorPrimitiveValue label p^2 ∂cubeMeasure d) = ∏ k, primitiveMass (label k) := by
  have hfun : (fun p => tensorPrimitiveValue label p^2) =
      (fun p => ∏ k, primitiveValue (label k) (p k)^2) := by
    funext p
    simp only [tensorPrimitiveValue, Finset.prod_pow]
  rw [hfun, cubeMeasure, integral_fintype_prod_eq_prod (fun k p => primitiveValue (label k) p^2)]
  simp_rw [integral_primitiveValue_sq]

/-- Exact product norm of the normalized tensor primitive. -/
theorem integral_normalizedTensorPrimitiveValue_sq {d H : ℕ} (label : TensorLabel d H) :
    (∫ p, normalizedTensorPrimitiveValue label p^2 ∂cubeMeasure d) =
      ∏ k, primitiveMass (label k)/mass (label k) := by
  have hfun : (fun p => normalizedTensorPrimitiveValue label p^2) =
      (fun p => ∏ k, normalizedPrimitiveValue (label k) (p k)^2) := by
    funext p
    simp only [normalizedTensorPrimitiveValue, Finset.prod_pow]
  rw [hfun, cubeMeasure, integral_fintype_prod_eq_prod (fun k p => normalizedPrimitiveValue (label k) p^2)]
  simp_rw [integral_normalizedPrimitiveValue_sq]

/-- The norm identity applies to the actual anchored-box operator, not only
to the explicit coordinate-product formula. -/
theorem integral_boxPrimitive_tensorValue_sq {d H : ℕ} (label : TensorLabel d H) :
    (∫ p, Tusnady.boxPrimitive (tensorValue label) p^2 ∂cubeMeasure d) =
      ∏ k, primitiveMass (label k) := by
  rw [← integral_tensorPrimitiveValue_sq label]
  apply integral_congr_ae
  filter_upwards [cubeMeasure_ae_unit d] with p hp
  rw [boxPrimitive_tensorValue label p (fun k => (hp k).2.le)]

/-- Actual anchored-box norm identity for the normalized L² tensor representatives. -/
theorem integral_boxPrimitive_normalizedTensorValue_sq {d H : ℕ} (label : TensorLabel d H) :
    (∫ p, Tusnady.boxPrimitive (normalizedTensorValue label) p^2 ∂cubeMeasure d) =
      ∏ k, primitiveMass (label k)/mass (label k) := by
  rw [← integral_normalizedTensorPrimitiveValue_sq label]
  apply integral_congr_ae
  filter_upwards [cubeMeasure_ae_unit d] with p hp
  rw [boxPrimitive_normalizedTensorValue label p (fun k => (hp k).2.le)]

end Tusnady.Haar
