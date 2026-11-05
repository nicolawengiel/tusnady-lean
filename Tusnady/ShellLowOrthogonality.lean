import Tusnady.LinearPrimitive
import Tusnady.HaarTentAffine

/-!
# Actual shell primitives are orthogonal to the low primitive Haar cross

Main.pdf Lemma 5.2(c), on concrete real functions. A low tensor has one
coordinate whose primitive is affine on the shell interval; the actual
vanishing primitive moments kill that factor.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace Tusnady.Witness
open DyadicFunctions Haar
variable {d h H : ℕ}

lemma haarPrimitive_affine_on_shell {a : ℕ} (i : Fin (2^a)) (L : Haar.Label H)
    (hL : Haar.level L < (a:ℤ)) :
    ∃ A B : ℝ, EqOn (Haar.normalizedPrimitiveValue L) (fun x => A*x+B) (dyadicInterval a i) := by
  have hraw : ∃ A B : ℝ, EqOn (Haar.primitiveValue L) (fun x => A*x+B) (dyadicInterval a i) := by
    cases L with
    | none =>
      refine ⟨-1,1,?_⟩
      intro x _
      simp only [Haar.primitiveValue]
      ring
    | some L =>
      rcases L with ⟨b,k⟩
      change (b.val:ℤ) < (a:ℤ) at hL
      have hb : b.val < a := by exact_mod_cast hL
      obtain ⟨A,B,hAB⟩ := Haar.tentI_affine_on_finer b.val a (by omega) k i
      refine ⟨-A,-B,?_⟩
      intro x hx
      change -Haar.tentI b.val k x = _
      rw [hAB hx]
      ring
  obtain ⟨A,B,hAB⟩ := hraw
  refine ⟨A/Real.sqrt (Haar.mass L), B/Real.sqrt (Haar.mass L), ?_⟩
  intro x hx
  unfold Haar.normalizedPrimitiveValue
  rw [hAB hx]
  ring

lemma integral_psiI_lowPrimitive (a : ℕ) (i : Fin (2^a)) (L : Haar.Label H)
    (hL : Haar.level L < (a:ℤ)) :
    (∫ x, psiI a i x * Haar.normalizedPrimitiveValue L x ∂Haar.unitMeasure) = 0 := by
  obtain ⟨A,B,hAB⟩ := haarPrimitive_affine_on_shell i L hL
  rw [Haar.integral_unitMeasure]
  exact psiI_orthogonal_affine_on a i _ A B hAB

lemma lowTensor_has_shallow_coordinate (R : Shell d h) (L : Haar.TensorLabel d H)
    (hL : Haar.tensorLevel L < (h:ℤ)) :
    ∃ k, Haar.level (L k) < (R.1.depth k:ℤ) := by
  by_contra! hge
  have hh : (h:ℤ) ≤ Haar.tensorLevel L := by
    calc
      (h:ℤ) = ∑ k, (R.1.depth k:ℤ) := by exact_mod_cast R.1.sum_depth.symm
      _ ≤ Haar.tensorLevel L := Finset.sum_le_sum fun k _ => hge k
  exact (not_lt_of_ge hh) hL

/-- Concrete shell primitive versus every actual low Haar primitive. -/
theorem normalizedPrimitive_orthogonal_lowTensor (R : Shell d h) (L : Haar.TensorLabel d H)
    (hL : Haar.tensorLevel L < (h:ℤ)) :
    (∫ x, normalizedPrimitive R x * Haar.normalizedTensorPrimitiveValue L x ∂Haar.cubeMeasure d) = 0 := by
  obtain ⟨k,hk⟩ := lowTensor_has_shallow_coordinate R L hL
  have heq (x : Point d) : normalizedPrimitive R x * Haar.normalizedTensorPrimitiveValue L x =
      (shellVolume h)⁻¹ * ∏ j, (psiI (R.1.depth j) (R.2 j) (x j) *
        Haar.normalizedPrimitiveValue (L j) (x j)) := by
    unfold normalizedPrimitive psiShell Haar.normalizedTensorPrimitiveValue
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [heq]
  rw [integral_const_mul, Haar.cubeMeasure,
    integral_fintype_prod_eq_prod (fun j x => psiI (R.1.depth j) (R.2 j) x *
      Haar.normalizedPrimitiveValue (L j) x)]
  have hz : (∏ j, ∫ x, psiI (R.1.depth j) (R.2 j) x *
      Haar.normalizedPrimitiveValue (L j) x ∂Haar.unitMeasure) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ k) (integral_psiI_lowPrimitive _ _ _ hk)
  rw [hz, mul_zero]

end Tusnady.Witness
