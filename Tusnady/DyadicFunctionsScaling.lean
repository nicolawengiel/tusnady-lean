import Tusnady.DyadicFunctionsPrimitive
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

/-! # Affine localization of the actual Walsh function and primitive. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.DyadicFunctions
open MeasureTheory Set
open scoped BigOperators

/-- Affine localization of the concrete three-bit Walsh function. -/
def q (c length x : ℝ) : ℝ := qBase ((x-c)/length)

/-- Affine localization of its actual primitive. -/
def psi (c length p : ℝ) : ℝ := length * psiBase ((p-c)/length)

/-- Change of variables for the actual Lebesgue integral. -/
theorem integral_affine_pullback (F : ℝ → ℝ) (c length : ℝ) (hl : 0 < length) :
    (∫ x, F ((x-c)/length)) = length * ∫ y, F y := by
  calc
    (∫ x, F ((x-c)/length)) = ∫ y, F (y/length) :=
      integral_sub_right_eq_self (fun y => F (y/length)) c
    _ = length * ∫ y, F y := by
      rw [Measure.integral_comp_div]
      simp only [abs_of_pos hl, smul_eq_mul]

lemma normalized_mem_unit_iff (c length x : ℝ) (hl : 0 < length) :
    (x-c)/length ∈ Ico (0:ℝ) 1 ↔ x ∈ Ico c (c+length) := by
  constructor
  · intro hx
    constructor
    · have h := (le_div_iff₀ hl).mp hx.1
      linarith
    · have h := (div_lt_iff₀ hl).mp hx.2
      linarith
  · intro hx
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hl.le
    · apply (div_lt_iff₀ hl).2
      linarith [hx.2]

/-- Exact absolute value on the localized half-open interval. -/
theorem abs_q (c length x : ℝ) (hl : 0 < length) :
    |q c length x| = (Ico c (c+length)).indicator (fun _ => (1:ℝ)) x := by
  rw [q, abs_qBase]
  by_cases hx : x ∈ Ico c (c+length)
  · have hn := (normalized_mem_unit_iff c length x hl).2 hx
    simp [hx, hn]
  · have hn : (x-c)/length ∉ Ico (0:ℝ) 1 :=
      fun h => hx ((normalized_mem_unit_iff c length x hl).1 h)
    simp [hx, hn]

/-- The primitive vanishes outside the localized interval. -/
theorem psi_zero_outside (c length p : ℝ) (hl : 0 < length)
    (hp : p ∉ Ico c (c+length)) : psi c length p = 0 := by
  unfold psi
  rw [psiBase_zero_outside _ (fun h => hp ((normalized_mem_unit_iff c length p hl).1 h))]
  simp

/-- Exact integral representation on the localized interval. -/
theorem psi_eq_primitive (c length p : ℝ) (hl : 0 < length) :
    psi c length p = ∫ x in p..c+length, q c length x := by
  have hlen : length ≠ 0 := ne_of_gt hl
  have hfun : (fun x => q c length x) = (fun x => qBase (x/length-c/length)) := by
    funext x
    unfold q
    congr 1
    ring
  rw [hfun, intervalIntegral.integral_comp_div_sub qBase hlen]
  have hend : (c+length)/length-c/length = (1:ℝ) := by field_simp; ring
  rw [hend]
  unfold psi
  rw [psiBase_eq_primitive]
  congr 2
  ring

lemma qBase_moment_integrable (n : ℕ) : Integrable (fun x => qBase x * x^n) := by
  have hsum : Integrable
      (fun x => ∑ i : Fin 8, patch i (fun y => walshSign i * y^n) x) :=
    integrable_finset_sum Finset.univ
      (fun i _ => patch_integrable i _ (by fun_prop))
  convert hsum using 1
  funext x
  unfold qBase
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact patch_mul i (fun _ => walshSign i) (fun y => y^n) x

lemma psiBase_moment_integrable (n : ℕ) : Integrable (fun x => psiBase x * x^n) := by
  have hsum : Integrable
      (fun x => ∑ i : Fin 8, patch i (fun y => primitivePiece i y * y^n) x) :=
    integrable_finset_sum Finset.univ
      (fun i _ => patch_integrable i _ (by unfold primitivePiece; fun_prop))
  convert hsum using 1
  funext x
  unfold psiBase
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact patch_mul i (primitivePiece i) (fun y => y^n) x

lemma psiBase_sq_integrable : Integrable (fun x => psiBase x^2) := by
  have hsum : Integrable
      (fun x => ∑ i : Fin 8, patch i (fun y => primitivePiece i y^2) x) :=
    integrable_finset_sum Finset.univ
      (fun i _ => patch_integrable i _ (by unfold primitivePiece; fun_prop))
  convert hsum using 1
  funext x
  exact square_patch_sum primitivePiece x

/-- The three base moments cancel against every affine-transformed monomial
of degree at most two. -/
lemma integral_qBase_affine_pow (c length : ℝ) (n : ℕ) (hn : n ≤ 2) :
    (∫ x, qBase x * (c+length*x)^n) = 0 := by
  interval_cases n
  · simpa only [pow_zero, mul_one] using integral_qBase
  · have hfun : (fun x => qBase x * (c+length*x)^1) =
        (fun x => c*qBase x + length*(qBase x*x)) := by funext x; ring
    have h₁ : Integrable (fun x => length*(qBase x*x)) := by
      simpa only [pow_one] using (qBase_moment_integrable 1).const_mul length
    rw [hfun, integral_add (qBase_integrable.const_mul c) h₁, integral_const_mul, integral_const_mul]
    simp only [integral_qBase, integral_qBase_mul_id, mul_zero, add_zero]
  · have hfun : (fun x => qBase x * (c+length*x)^2) =
        (fun x => (c^2*qBase x + (2*c*length)*(qBase x*x)) + length^2*(qBase x*x^2)) := by
      funext x
      ring
    have h₀ := qBase_integrable.const_mul (c^2)
    have h₁ : Integrable (fun x => (2*c*length)*(qBase x*x)) := by
      simpa only [pow_one] using (qBase_moment_integrable 1).const_mul (2*c*length)
    have h₂ := (qBase_moment_integrable 2).const_mul (length^2)
    have hsum : Integrable (fun x => c^2*qBase x + (2*c*length)*(qBase x*x)) := h₀.add h₁
    rw [hfun, integral_add hsum h₂, integral_add h₀ h₁,
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp only [integral_qBase, integral_qBase_mul_id, integral_qBase_mul_sq, mul_zero, add_zero]

/-- All three required moments vanish for every positive-length localization. -/
theorem integral_q_moment (c length : ℝ) (hl : 0 < length) (n : ℕ) (hn : n ≤ 2) :
    (∫ x, q c length x * x^n) = 0 := by
  have hnorm : ∀ x : ℝ, c+length*((x-c)/length) = x := by
    intro x
    field_simp
    ring
  have hfun : (fun x => q c length x * x^n) =
      (fun x => (fun u => qBase u * (c+length*u)^n) ((x-c)/length)) := by
    funext x
    dsimp only
    rw [hnorm]
    rfl
  rw [hfun, integral_affine_pullback (fun u => qBase u*(c+length*u)^n) c length hl,
    integral_qBase_affine_pow c length n hn, mul_zero]

lemma integral_psiBase_affine (c length : ℝ) :
    (∫ x, psiBase x * (c+length*x)) = 0 := by
  have hfun : (fun x => psiBase x * (c+length*x)) =
      (fun x => c*psiBase x + length*(psiBase x*x)) := by funext x; ring
  have h₁ : Integrable (fun x => length*(psiBase x*x)) := by
    simpa only [pow_one] using (psiBase_moment_integrable 1).const_mul length
  rw [hfun, integral_add (psiBase_integrable.const_mul c) h₁,
    integral_const_mul, integral_const_mul, integral_psiBase, integral_psiBase_mul_id]
  ring

/-- Zeroth primitive moment after affine localization. -/
theorem integral_psi (c length : ℝ) (hl : 0 < length) :
    (∫ x, psi c length x) = 0 := by
  unfold psi
  rw [integral_const_mul, integral_affine_pullback _ c length hl, integral_psiBase]
  ring

/-- First primitive moment after affine localization. -/
theorem integral_psi_mul_id (c length : ℝ) (hl : 0 < length) :
    (∫ x, psi c length x * x) = 0 := by
  have hnorm : ∀ x : ℝ, c+length*((x-c)/length) = x := by
    intro x
    field_simp
    ring
  have hfun : (fun x => psi c length x * x) =
      (fun x => length * (fun u => psiBase u * (c+length*u)) ((x-c)/length)) := by
    funext x
    dsimp only
    rw [hnorm]
    unfold psi
    ring
  rw [hfun, integral_const_mul, integral_affine_pullback (fun u => psiBase u*(c+length*u)) c length hl,
    integral_psiBase_affine]
  ring

/-- Exact squared norm: the `length³/192` constant in Manuscript Lemma 2.2. -/
theorem integral_psi_sq (c length : ℝ) (hl : 0 < length) :
    (∫ x, psi c length x^2) = length^3/192 := by
  have hfun : (fun x => psi c length x^2) =
      (fun x => length^2 * (fun u => psiBase u^2) ((x-c)/length)) := by
    funext x
    unfold psi
    ring
  rw [hfun, integral_const_mul, integral_affine_pullback (fun u => psiBase u^2) c length hl, integral_psiBase_sq]
  ring

/-- A localized primitive is affine on the eight corresponding real cells. -/
theorem psi_affine_on_eighth (c length : ℝ) (hl : 0 < length) (i : Fin 8) :
    EqOn (psi c length)
      (fun x => -walshSign i*x + (walshSign i*c + length*primitiveIntercept i))
      (Ico (c+length*cellLo i) (c+length*cellHi i)) := by
  intro x hx
  have hcell : (x-c)/length ∈ baseCell i := by
    constructor
    · apply (le_div_iff₀ hl).2
      linarith [hx.1]
    · apply (div_lt_iff₀ hl).2
      linarith [hx.2]
  unfold psi
  rw [psiBase_on_cell i _ hcell]
  field_simp
  ring

/-- Left endpoint of an actual dyadic interval. -/
def dyadicLeft (a : ℕ) (i : Fin (2^a)) : ℝ := (i.val : ℝ)/(2:ℝ)^a

/-- Positive length of an actual dyadic interval. -/
def dyadicLength (a : ℕ) : ℝ := 1/(2:ℝ)^a

lemma dyadicLength_pos (a : ℕ) : 0 < dyadicLength a := by unfold dyadicLength; positivity

/-- The dyadic interval as the actual reals `[i·2⁻ᵃ,(i+1)·2⁻ᵃ)`. -/
def dyadicInterval (a : ℕ) (i : Fin (2^a)) : Set ℝ :=
  Ico (dyadicLeft a i) (dyadicLeft a i + dyadicLength a)

def qI (a : ℕ) (i : Fin (2^a)) : ℝ → ℝ := q (dyadicLeft a i) (dyadicLength a)
def psiI (a : ℕ) (i : Fin (2^a)) : ℝ → ℝ := psi (dyadicLeft a i) (dyadicLength a)

/-- Concrete dyadic Walsh moments, with no abstract function assumptions. -/
theorem integral_qI_moment (a : ℕ) (i : Fin (2^a)) (n : ℕ) (hn : n ≤ 2) :
    (∫ x, qI a i x*x^n) = 0 := integral_q_moment _ _ (dyadicLength_pos a) n hn

/-- Exact norm of the primitive of every concrete dyadic interval. -/
theorem integral_psiI_sq (a : ℕ) (i : Fin (2^a)) :
    (∫ x, psiI a i x^2) = dyadicLength a^3/192 := integral_psi_sq _ _ (dyadicLength_pos a)

end Tusnady.DyadicFunctions
