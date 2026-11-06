import Tusnady.HaarOrthogonality
import Mathlib.MeasureTheory.Integral.Pi

/-!
# A finite family of actual tensor Haar functions

The construction includes the constant function and all Haar intervals of
depth strictly below `H`. Orthogonality is proved with actual real Lebesgue
integrals on the product unit cube, not assumed as a finite-matrix property.
No infinite Haar basis or completeness assumption is used.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators NNReal ENNReal

/-- Lebesgue measure on the half-open unit interval. -/
def unitMeasure : Measure ℝ := volume.restrict (Ico (0:ℝ) 1)

instance unitMeasure_probability : IsProbabilityMeasure unitMeasure := by
  constructor
  norm_num [unitMeasure]

lemma integral_unitMeasure (f : ℝ → ℝ) :
    (∫ x, f x ∂unitMeasure) = ∫ x in (0:ℝ)..1, f x := by
  rw [unitMeasure, ← integral_Icc_eq_integral_Ico, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- `none` denotes the constant and `some (depth,index)` a genuine Haar
interval. This is a concrete finite type. -/
abbrev Label (H : ℕ) := Option (Σ a : Fin H, Fin (2^a.val))

def value {H : ℕ} (label : Label H) (x : ℝ) : ℝ :=
  match label with
  | none => 1
  | some ⟨a, i⟩ => hI a.val i x

def mass {H : ℕ} (label : Label H) : ℝ :=
  match label with
  | none => 1
  | some ⟨a, _⟩ => dyadicLength a.val

/-- Levels use the manuscript's constant level -1. -/
def level {H : ℕ} (label : Label H) : ℤ :=
  match label with
  | none => -1
  | some ⟨a, _⟩ => (a.val : ℤ)

lemma mass_pos {H : ℕ} (label : Label H) : 0 < mass label := by
  cases label with
  | none => norm_num [mass]
  | some label => exact dyadicLength_pos label.1.val

/-- Exact univariate integral Gram matrix for the finite Haar family. -/
theorem integral_value_mul {H : ℕ} (L K : Label H) :
    (∫ x, value L x*value K x ∂unitMeasure) = if L = K then mass L else 0 := by
  classical
  rw [integral_unitMeasure]
  cases L with
  | none =>
    cases K with
    | none => simp [value, mass]
    | some K =>
      rcases K with ⟨b,j⟩
      simpa only [value, one_mul, reduceCtorEq, if_false] using integral_unit_hI b.val j
  | some L =>
    rcases L with ⟨a,i⟩
    cases K with
    | none =>
      simpa only [value, mul_one, reduceCtorEq, if_false] using integral_unit_hI a.val i
    | some K =>
      rcases K with ⟨b,j⟩
      by_cases hab : a = b
      · subst b
        by_cases hij : i = j
        · subst j
          simpa only [value, mass, if_pos rfl, ite_true, pow_two] using integral_unit_hI_sq a.val i
        · have hne : (some ⟨a,i⟩ : Label H) ≠ some ⟨a,j⟩ := by
            intro h
            have hv := congrArg (fun l : Label H => match l with | none => 0 | some p => p.2.val) h
            exact hij (Fin.ext hv)
          rw [if_neg hne]
          exact integral_unit_hI_mul_hI_same_depth a.val i j hij
      · have hne : (some ⟨a,i⟩ : Label H) ≠ some ⟨b,j⟩ := by
          intro h
          exact hab (congrArg Sigma.fst (Option.some.inj h))
        rw [if_neg hne]
        have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
        rcases lt_or_gt_of_ne hv with h | h
        · exact integral_unit_hI_mul_hI_separated a.val b.val h i j
        · simpa only [value, mul_comm] using integral_unit_hI_mul_hI_separated b.val a.val h j i

/-- Normalize each actual Haar function by its proved positive L² mass. -/
def normalizedValue {H : ℕ} (label : Label H) (x : ℝ) : ℝ :=
  value label x / Real.sqrt (mass label)

/-- Actual integral orthonormality after normalization. -/
theorem integral_normalizedValue_mul {H : ℕ} (L K : Label H) :
    (∫ x, normalizedValue L x*normalizedValue K x ∂unitMeasure) = if L = K then 1 else 0 := by
  classical
  have hfun : (fun x => normalizedValue L x*normalizedValue K x) =
      (fun x => (1/(Real.sqrt (mass L)*Real.sqrt (mass K)))*(value L x*value K x)) := by
    funext x
    unfold normalizedValue
    ring
  rw [hfun, integral_const_mul, integral_value_mul]
  by_cases heq : L = K
  · subst K
    rw [Real.mul_self_sqrt (mass_pos L).le]
    simp [ne_of_gt (mass_pos L)]
  · simp only [if_neg heq, mul_zero]

/-- Finite tensor labels, one concrete univariate Haar label per coordinate. -/
abbrev TensorLabel (d H : ℕ) := Fin d → Label H

/-- Actual product Lebesgue measure on the unit cube. -/
def cubeMeasure (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => unitMeasure)

instance cubeMeasure_probability (d : ℕ) : IsProbabilityMeasure (cubeMeasure d) := by
  unfold cubeMeasure
  infer_instance

def tensorValue {d H : ℕ} (label : TensorLabel d H) (x : Fin d → ℝ) : ℝ :=
  ∏ k, value (label k) (x k)

def normalizedTensorValue {d H : ℕ} (label : TensorLabel d H) (x : Fin d → ℝ) : ℝ :=
  ∏ k, normalizedValue (label k) (x k)

def tensorMass {d H : ℕ} (label : TensorLabel d H) : ℝ := ∏ k, mass (label k)
def tensorLevel {d H : ℕ} (label : TensorLabel d H) : ℤ := ∑ k, level (label k)

/-- Fubini gives the exact integral Gram matrix of the actual normalized
tensor family, in every dimension including zero. -/
theorem integral_normalizedTensorValue_mul {d H : ℕ} (L K : TensorLabel d H) :
    (∫ x, normalizedTensorValue L x*normalizedTensorValue K x ∂cubeMeasure d) =
      if L = K then 1 else 0 := by
  classical
  have hfun : (fun x => normalizedTensorValue L x*normalizedTensorValue K x) =
      (fun x => ∏ k, (normalizedValue (L k) (x k)*normalizedValue (K k) (x k))) := by
    funext x
    exact Finset.prod_mul_distrib.symm
  rw [hfun, cubeMeasure, integral_fintype_prod_eq_prod
    (fun k x => normalizedValue (L k) x*normalizedValue (K k) x)]
  simp_rw [integral_normalizedValue_mul]
  by_cases heq : L = K
  · subst K
    simp
  · rw [if_neg heq]
    have hex : ∃ k, L k ≠ K k := by
      by_contra h
      apply heq
      funext k
      exact not_not.mp (not_exists.mp h k)
    obtain ⟨k,hk⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- The scalar family has exactly one member per cell of the depth-H grid. -/
theorem card_label (H : ℕ) : Fintype.card (Label H) = 2^H := by
  have hsum : (∑ a : Fin H, (2:ℕ)^a.val)+1 = 2^H := by
    induction H with
    | zero => simp
    | succ H ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc, Fin.val_last]
      rw [pow_succ]
      omega
  simpa only [Label, Fintype.card_option, Fintype.card_sigma, Fintype.card_fin] using hsum

/-- The tensor family has exactly the cardinality of the product raster. -/
theorem card_tensorLabel (d H : ℕ) : Fintype.card (TensorLabel d H) = 2^(H*d) := by
  rw [Fintype.card_fun, card_label, Fintype.card_fin, pow_mul]

/-- The finite low-cross index set. All its membership conditions and levels
are explicit; using it as an orthogonal projection needs no infinite basis. -/
def lowCrossLabels (d H h : ℕ) : Finset (TensorLabel d H) :=
  Finset.univ.filter (fun label => tensorLevel label ≤ (h:ℤ)-1)

end Tusnady.Haar
