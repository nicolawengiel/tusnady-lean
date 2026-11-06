import Tusnady.HaarFiniteCombination

/-!
# Concrete mixed Walsh/Haar/constant factors for cell-location estimates

Each factor has a proved finite Haar expansion at one exact level. Thus an
actual mixed tensor is retained or removed by the genuine high projection
according to its computed total level. Its actual primitive norm is a product
of the proved one-dimensional constants; no cell-location conclusion is
postulated as a hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.DyadicFunctions Tusnady.Haar
open scoped BigOperators

inductive Factor (H : ℕ) where
  | constant (c : ℝ)
  | haar (a : Fin H) (i : Fin (2^a.val)) (c : ℝ)
  | walsh (a : ℕ) (ha : a+2 < H) (i : Fin (2^a)) (c : ℝ)

def factorValue {H : ℕ} (f : Factor H) (x : ℝ) : ℝ :=
  match f with
  | .constant c => c
  | .haar a i c => c*hI a.val i x
  | .walsh a _ i c => c*qI a i x

def factorLevel {H : ℕ} (f : Factor H) : ℤ :=
  match f with
  | .constant _ => -1
  | .haar a _ _ => (a.val:ℤ)
  | .walsh a _ _ _ => ((a+2:ℕ):ℤ)

def quarterSign : Fin 4 → ℝ := ![1,-1,-1,1]

def termLabel {H : ℕ} (f : Factor H) (t : Fin 4) : Label H :=
  match f with
  | .constant _ => none
  | .haar a i _ => some ⟨a,i⟩
  | .walsh a ha i _ => some ⟨⟨a+2,ha⟩,refineIndex a 2 i t⟩

def termCoefficient {H : ℕ} (f : Factor H) (t : Fin 4) : ℝ :=
  match f with
  | .constant c => if t.val = 0 then c else 0
  | .haar _ _ c => if t.val = 0 then c else 0
  | .walsh _ _ _ c => c*quarterSign t

def normalizedCoefficient {H : ℕ} (f : Factor H) (t : Fin 4) : ℝ :=
  termCoefficient f t * Real.sqrt (mass (termLabel f t))

@[simp] theorem termLabel_level {H : ℕ} (f : Factor H) (t : Fin 4) :
    level (termLabel f t) = factorLevel f := by
  cases f <;> rfl

/-- Every concrete factor is exactly a four-term raw Haar combination. Zero
coefficients use labels at the same level, preserving the level invariant. -/
theorem factor_raw_expansion {H : ℕ} (f : Factor H) (x : ℝ) :
    factorValue f x = ∑ t : Fin 4, termCoefficient f t*value (termLabel f t) x := by
  cases f with
  | constant c => norm_num [factorValue, termCoefficient, termLabel, value, Fin.sum_univ_succ]
  | haar a i c => norm_num [factorValue, termCoefficient, termLabel, value, Fin.sum_univ_succ]
  | walsh a ha i c =>
    rw [factorValue, qI_eq_four_haar]
    norm_num [termCoefficient, termLabel, value, quarterSign, Fin.sum_univ_succ]
    ring

lemma normalized_term {H : ℕ} (f : Factor H) (t : Fin 4) (x : ℝ) :
    normalizedCoefficient f t*normalizedValue (termLabel f t) x =
      termCoefficient f t*value (termLabel f t) x := by
  have hs : Real.sqrt (mass (termLabel f t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (mass_pos _))
  unfold normalizedCoefficient normalizedValue
  field_simp

/-- Exact factor expansion in the actual normalized L² representatives. -/
theorem factor_expansion {H : ℕ} (f : Factor H) (x : ℝ) :
    factorValue f x = ∑ t : Fin 4, normalizedCoefficient f t*normalizedValue (termLabel f t) x := by
  rw [factor_raw_expansion]
  apply Finset.sum_congr rfl
  intro t _
  exact (normalized_term f t x).symm

def factorPrimitive {H : ℕ} (f : Factor H) (p : ℝ) : ℝ :=
  match f with
  | .constant c => c*(1-p)
  | .haar a i c => c*(-tentI a.val i p)
  | .walsh a _ i c => c*psiI a i p

def factorPrimitiveMass {H : ℕ} (f : Factor H) : ℝ :=
  match f with
  | .constant c => c^2/3
  | .haar a _ c => c^2*dyadicLength a.val^3/12
  | .walsh a _ _ c => c^2*dyadicLength a^3/192

lemma integral_factorValue_right {H : ℕ} (f : Factor H) (p : ℝ) :
    (∫ x in p..1, factorValue f x) = factorPrimitive f p := by
  cases f with
  | constant c => simp [factorValue, factorPrimitive, intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  | haar a i c =>
    change (∫ x in p..1, c*hI a.val i x) = c*(-tentI a.val i p)
    rw [intervalIntegral.integral_const_mul, integral_hI_right_unit]
  | walsh a ha i c =>
    change (∫ x in p..1, c*qI a i x) = c*psiI a i p
    rw [intervalIntegral.integral_const_mul, ← psiI_eq_primitive_unit]

lemma integral_factorPrimitive_sq {H : ℕ} (f : Factor H) :
    (∫ p, factorPrimitive f p^2 ∂unitMeasure) = factorPrimitiveMass f := by
  cases f with
  | constant c =>
    change (∫ p, (c*(1-p))^2 ∂unitMeasure) = c^2/3
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have h := integral_primitiveValue_sq (none : Label H)
    change (∫ p, (1-p)^2 ∂unitMeasure) = (1:ℝ)/3 at h
    rw [h]
    ring
  | haar a i c =>
    change (∫ p, (c*(-tentI a.val i p))^2 ∂unitMeasure) = c^2*dyadicLength a.val^3/12
    simp_rw [mul_pow]
    rw [integral_const_mul]
    have h := integral_primitiveValue_sq (some ⟨a,i⟩ : Label H)
    change (∫ p, (-tentI a.val i p)^2 ∂unitMeasure) = dyadicLength a.val^3/12 at h
    rw [h]
    ring
  | walsh a ha i c =>
    change (∫ p, (c*psiI a i p)^2 ∂unitMeasure) = c^2*dyadicLength a^3/192
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_unitMeasure, integral_unit_psiI_sq]
    ring

abbrev Choices (d : ℕ) := Fin d → Fin 4

def choiceLabel {d H : ℕ} (f : Fin d → Factor H) (t : Choices d) : TensorLabel d H :=
  fun k => termLabel (f k) (t k)

def choiceCoefficient {d H : ℕ} (f : Fin d → Factor H) (t : Choices d) : ℝ :=
  ∏ k, normalizedCoefficient (f k) (t k)

def tensorFactorValue {d H : ℕ} (f : Fin d → Factor H) (x : Fin d → ℝ) : ℝ :=
  ∏ k, factorValue (f k) (x k)

def tensorFactorLevel {d H : ℕ} (f : Fin d → Factor H) : ℤ := ∑ k, factorLevel (f k)

def tensorFactorPrimitive {d H : ℕ} (f : Fin d → Factor H) (p : Fin d → ℝ) : ℝ :=
  ∏ k, factorPrimitive (f k) (p k)

@[simp] theorem choiceLabel_level {d H : ℕ} (f : Fin d → Factor H) (t : Choices d) :
    tensorLevel (choiceLabel f t) = tensorFactorLevel f := by
  unfold tensorLevel choiceLabel tensorFactorLevel
  simp only [termLabel_level]

/-- Concrete product expansion; no tensor-basis expansion premise. -/
theorem tensorFactor_expansion {d H : ℕ} (f : Fin d → Factor H) (x : Fin d → ℝ) :
    tensorFactorValue f x =
      combinationFunction Finset.univ (choiceCoefficient f) (choiceLabel f) x := by
  unfold tensorFactorValue
  simp_rw [factor_expansion]
  rw [Fintype.prod_sum]
  unfold combinationFunction choiceCoefficient normalizedTensorValue choiceLabel
  apply Finset.sum_congr rfl
  intro t _
  exact Finset.prod_mul_distrib

/-- The actual L² vector of the mixed tensor, built from its proved expansion. -/
def tensorFactorL2 {d H : ℕ} (f : Fin d → Factor H) : Lp ℝ 2 (cubeMeasure d) :=
  combinationL2 Finset.univ (choiceCoefficient f) (choiceLabel f)

theorem tensorFactorL2_ae {d H : ℕ} (f : Fin d → Factor H) :
    tensorFactorL2 f =ᵐ[cubeMeasure d] tensorFactorValue f := by
  exact (combination_ae Finset.univ (choiceCoefficient f) (choiceLabel f)).trans
    (Filter.Eventually.of_forall (fun x => (tensorFactor_expansion f x).symm))

/-- The computed exact level controls the genuine high projection of every
concrete mixed tensor. -/
theorem highProjection_tensorFactor {d H : ℕ} (h : ℕ) (f : Fin d → Factor H) :
    highProjection d H h (tensorFactorL2 f) =
      if (h:ℤ) ≤ tensorFactorLevel f then tensorFactorL2 f else 0 := by
  classical
  unfold tensorFactorL2
  rw [highProjection_combination]
  unfold combinationL2 retainedCoefficient
  simp_rw [choiceLabel_level]
  by_cases hl : (h:ℤ) ≤ tensorFactorLevel f <;> simp [hl]

/-- The explicit tensor primitive is the project's actual anchored primitive. -/
theorem boxPrimitive_tensorFactor {d H : ℕ} (f : Fin d → Factor H) (p : Tusnady.Point d)
    (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive (tensorFactorValue f) p = tensorFactorPrimitive f p := by
  unfold tensorFactorValue tensorFactorPrimitive
  rw [Tusnady.boxPrimitive_tensor_interval (fun k => factorValue (f k)) p (fun k => (hp k).2)]
  simp_rw [integral_factorValue_right]

/-- Exact primitive of the actual high projection, including the removed case. -/
theorem boxPrimitive_high_tensorFactor {d H : ℕ} (h : ℕ) (f : Fin d → Factor H)
    (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive (highProjection d H h (tensorFactorL2 f)) p =
      if (h:ℤ) ≤ tensorFactorLevel f then tensorFactorPrimitive f p else 0 := by
  rw [highProjection_tensorFactor]
  by_cases hl : (h:ℤ) ≤ tensorFactorLevel f
  · rw [if_pos hl, if_pos hl]
    rw [boxPrimitive_congr_cube_ae _ _ (tensorFactorL2_ae f) p hp]
    exact boxPrimitive_tensorFactor f p hp
  · rw [if_neg hl, if_neg hl]
    have hzero : (0 : Lp ℝ 2 (cubeMeasure d)) =ᵐ[cubeMeasure d] (fun _ => (0:ℝ)) :=
      Lp.coeFn_zero ℝ 2 (cubeMeasure d)
    rw [boxPrimitive_congr_cube_ae _ _ hzero p hp]
    simp [Tusnady.boxPrimitive]

/-- Exact mixed tensor primitive norm from the concrete one-dimensional table. -/
theorem integral_tensorFactorPrimitive_sq {d H : ℕ} (f : Fin d → Factor H) :
    (∫ p, tensorFactorPrimitive f p^2 ∂cubeMeasure d) = ∏ k, factorPrimitiveMass (f k) := by
  have hfun : (fun p => tensorFactorPrimitive f p^2) =
      (fun p => ∏ k, factorPrimitive (f k) (p k)^2) := by
    funext p
    simp only [tensorFactorPrimitive, Finset.prod_pow]
  rw [hfun, cubeMeasure, integral_fintype_prod_eq_prod (fun k p => factorPrimitive (f k) p^2)]
  simp_rw [integral_factorPrimitive_sq]

end Tusnady.Cell
