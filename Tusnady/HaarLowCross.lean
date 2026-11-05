import Tusnady.HaarPrimitiveCongruence

/-!
# Exhaustion of the manuscript's low Haar cross by a finite depth cap

The unbounded labels here describe all actual one-dimensional Haar functions,
including the constant at level -1. The low total-level condition itself
bounds every coordinate. Thus the finite model does not discard any low
Haar tensor from the manuscript.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Haar
open MeasureTheory Set
open Tusnady.DyadicFunctions
open scoped BigOperators

abbrev RawLabel := Option (Σ a : ℕ, Fin (2^a))
abbrev RawTensorLabel (d : ℕ) := Fin d → RawLabel

def rawLevel (label : RawLabel) : ℤ :=
  match label with
  | none => -1
  | some ⟨a,_⟩ => (a:ℤ)

def rawValue (label : RawLabel) (x : ℝ) : ℝ :=
  match label with
  | none => 1
  | some ⟨a,i⟩ => hI a i x

def rawTensorLevel {d : ℕ} (label : RawTensorLabel d) : ℤ := ∑ k, rawLevel (label k)
def rawTensorValue {d : ℕ} (label : RawTensorLabel d) (x : Fin d → ℝ) : ℝ :=
  ∏ k, rawValue (label k) (x k)

lemma rawLevel_add_one_nonneg (label : RawLabel) : 0 ≤ rawLevel label+1 := by
  cases label with
  | none => norm_num [rawLevel]
  | some label => simp only [rawLevel]; omega

/-- The shifted levels are nonnegative; a single coordinate cannot exceed
the total shifted level. This supplies the explicit finite depth bound. -/
lemma raw_coordinate_level_bound {d : ℕ} (label : RawTensorLabel d) (i : Fin d) :
    rawLevel (label i)+1 ≤ rawTensorLevel label+(d:ℤ) := by
  have h := Finset.single_le_sum
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin d))) => rawLevel_add_one_nonneg (label k))
    (Finset.mem_univ i)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, rawTensorLevel] using h

/-- Every nonconstant low coordinate has depth at most h+d-2, so any cap
H≥h+d-1 captures it. All arithmetic is over ℤ to preserve level -1. -/
lemma raw_low_coordinate_lt {d h H : ℕ} (label : RawTensorLabel d)
    (hlevel : rawTensorLevel label ≤ (h:ℤ)-1)
    (hcap : (h:ℤ)+(d:ℤ)-1 ≤ (H:ℤ)) (i : Fin d) : rawLevel (label i) < (H:ℤ) := by
  have h := raw_coordinate_level_bound label i
  omega

/-- Bound an actual Haar label using its proved level bound. -/
def labelOfRaw {H : ℕ} (label : RawLabel) (hlevel : rawLevel label < (H:ℤ)) : Label H :=
  match label with
  | none => none
  | some ⟨a,i⟩ => some ⟨⟨a, by change (a:ℤ) < (H:ℤ) at hlevel; exact_mod_cast hlevel⟩, i⟩

@[simp] lemma labelOfRaw_level {H : ℕ} (label : RawLabel) (hlevel : rawLevel label < (H:ℤ)) :
    level (labelOfRaw label hlevel) = rawLevel label := by
  cases label <;> rfl

@[simp] lemma labelOfRaw_value {H : ℕ} (label : RawLabel) (hlevel : rawLevel label < (H:ℤ)) (x : ℝ) :
    value (labelOfRaw label hlevel) x = rawValue label x := by
  cases label <;> rfl

def boundRawTensor {d h H : ℕ} (label : RawTensorLabel d)
    (hlevel : rawTensorLevel label ≤ (h:ℤ)-1)
    (hcap : (h:ℤ)+(d:ℤ)-1 ≤ (H:ℤ)) : TensorLabel d H :=
  fun i => labelOfRaw (label i) (raw_low_coordinate_lt label hlevel hcap i)

@[simp] lemma boundRawTensor_level {d h H : ℕ} (label : RawTensorLabel d)
    (hlevel : rawTensorLevel label ≤ (h:ℤ)-1)
    (hcap : (h:ℤ)+(d:ℤ)-1 ≤ (H:ℤ)) :
    tensorLevel (boundRawTensor label hlevel hcap) = rawTensorLevel label := by
  unfold tensorLevel rawTensorLevel boundRawTensor
  simp only [labelOfRaw_level]

@[simp] lemma boundRawTensor_value {d h H : ℕ} (label : RawTensorLabel d)
    (hlevel : rawTensorLevel label ≤ (h:ℤ)-1)
    (hcap : (h:ℤ)+(d:ℤ)-1 ≤ (H:ℤ)) (x : Fin d → ℝ) :
    tensorValue (boundRawTensor label hlevel hcap) x = rawTensorValue label x := by
  unfold tensorValue rawTensorValue boundRawTensor
  simp only [labelOfRaw_value]

def rawOfLabel {H : ℕ} (label : Label H) : RawLabel :=
  match label with
  | none => none
  | some ⟨a,i⟩ => some ⟨a.val,i⟩

@[simp] lemma rawOfLabel_level {H : ℕ} (label : Label H) : rawLevel (rawOfLabel label) = level label := by
  cases label <;> rfl

@[simp] lemma rawOfLabel_value {H : ℕ} (label : Label H) (x : ℝ) :
    rawValue (rawOfLabel label) x = value label x := by
  cases label <;> rfl

/-- The entire unbounded physical low-tensor family of the manuscript. -/
def rawLowFamily (d h : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  {f | ∃ label : RawTensorLabel d, rawTensorLevel label ≤ (h:ℤ)-1 ∧ f = rawTensorValue label}

/-- The finite physical low family selected by the explicit label filter. -/
def finiteLowFamily (d H h : ℕ) : Set ((Fin d → ℝ) → ℝ) :=
  tensorValue '' (lowCrossLabels d H h : Set (TensorLabel d H))

/-- No low tensor is lost by the finite depth cap. The equality is of
actual sets of real functions on the whole ambient space. -/
theorem rawLowFamily_eq_finiteLowFamily (d H h : ℕ)
    (hcap : (h:ℤ)+(d:ℤ)-1 ≤ (H:ℤ)) : rawLowFamily d h = finiteLowFamily d H h := by
  ext f
  constructor
  · rintro ⟨label,hlevel,rfl⟩
    refine ⟨boundRawTensor label hlevel hcap, ?_, ?_⟩
    · simp only [lowCrossLabels, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
        boundRawTensor_level]
      exact hlevel
    · funext x
      exact boundRawTensor_value label hlevel hcap x
  · rintro ⟨label,hlabel,rfl⟩
    refine ⟨fun k => rawOfLabel (label k), ?_, ?_⟩
    · have hl : tensorLevel label ≤ (h:ℤ)-1 := by
        simpa only [lowCrossLabels, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] using hlabel
      simpa only [rawTensorLevel, rawOfLabel_level, tensorLevel] using hl
    · funext x
      simp only [rawTensorValue, tensorValue, rawOfLabel_value]

/-- Equality of the corresponding physical linear spaces. -/
theorem lowCross_physical_spans_eq (d H h : ℕ)
    (hcap : (h:ℤ)+(d:ℤ)-1 ≤ (H:ℤ)) :
    Submodule.span ℝ (rawLowFamily d h) = Submodule.span ℝ (finiteLowFamily d H h) := by
  rw [rawLowFamily_eq_finiteLowFamily d H h hcap]

/-- The cap h+3d used by the manuscript also captures the whole low cross. -/
theorem rawLowFamily_cap_h_add_three_d (d h : ℕ) :
    rawLowFamily d h = finiteLowFamily d (h+3*d) h := by
  apply rawLowFamily_eq_finiteLowFamily
  omega

end Tusnady.Haar
