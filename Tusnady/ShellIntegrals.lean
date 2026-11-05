import Tusnady.Shell
import Tusnady.Primitive
import Tusnady.HaarTensor

/-!
# Actual tensor primitives and their orthogonality

Main.pdf §3.1, including Lemma 3.1. Integrals are with respect to the
actual product Lebesgue measure on the unit cube. No orthogonality or
primitive-evaluation hypothesis is supplied by the caller.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.Witness
open Dyadic DyadicFunctions

theorem measurable_qBase : Measurable qBase := by
  unfold qBase
  exact Finset.measurable_sum _ fun i _ => measurable_const.indicator measurableSet_Ico

theorem measurable_qI (a : ℕ) (i : Fin (2 ^ a)) : Measurable (qI a i) := by
  unfold qI q
  exact measurable_qBase.comp ((measurable_id.sub measurable_const).div_const _)

theorem measurable_qShell (R : Shell d h) : Measurable (qShell R) := by
  unfold qShell
  exact Finset.measurable_prod _ fun j _ => (measurable_qI _ _).comp (measurable_pi_apply j)

theorem continuous_psiShell (R : Shell d h) : Continuous (psiShell R) := by
  unfold psiShell
  exact continuous_finset_prod _ fun j _ => (psiI_continuous _ _).comp (continuous_apply j)

theorem continuous_normalizedPrimitive (R : Shell d h) : Continuous (normalizedPrimitive R) :=
  continuous_const.mul (continuous_psiShell R)

/-- The common volume is the product of the actual real side lengths. -/
theorem prod_sideLengths (r : Shape d h) :
    (∏ j, dyadicLength (r.depth j)) = shellVolume h := by
  unfold dyadicLength shellVolume
  simp only [one_div]
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, r.sum_depth]

/-- The concrete q_R has precisely its claimed primitive on the cube. -/
theorem boxPrimitive_qShell (R : Shell d h) (p : Point d) (hp : p ∈ UnitCube d) :
    boxPrimitive (qShell R) p = psiShell R p := by
  unfold qShell psiShell
  rw [boxPrimitive_tensor_interval _ p (fun j => (hp j).2)]
  apply Finset.prod_congr rfl
  intro j _
  exact (psiI_eq_primitive_unit _ _ _).symm

theorem boxPrimitive_qShell_normalized (R : Shell d h) (p : Point d)
    (hp : p ∈ UnitCube d) :
    boxPrimitive (qShell R) p = shellVolume h * normalizedPrimitive R p := by
  rw [boxPrimitive_qShell R p hp]
  unfold normalizedPrimitive
  field_simp [(shellVolume_pos h).ne']

/-- A supported real function has the same full-line and unit integrals. -/
theorem integral_unit_of_zero_outside (f : ℝ → ℝ)
    (hf : ∀ x, x ∉ Ico (0 : ℝ) 1 → f x = 0) :
    (∫ x, f x ∂Haar.unitMeasure) = ∫ x, f x := by
  rw [Haar.unitMeasure, ← integral_indicator measurableSet_Ico]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Ico (0 : ℝ) 1
  · simp [hx]
  · simp [hx, hf x hx]

theorem integral_unit_abs_qI (a : ℕ) (i : Fin (2 ^ a)) :
    (∫ x, |qI a i x| ∂Haar.unitMeasure) = dyadicLength a := by
  rw [integral_unit_of_zero_outside]
  · exact integral_abs_qI a i
  · intro x hx
    rw [qI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h))]
    simp

theorem integral_unit_qI_sq (a : ℕ) (i : Fin (2 ^ a)) :
    (∫ x, qI a i x ^ 2 ∂Haar.unitMeasure) = dyadicLength a := by
  rw [integral_unit_of_zero_outside]
  · exact integral_qI_sq a i
  · intro x hx
    rw [qI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h))]
    simp

/-- The actual L1 norm of each shell function is its common volume. -/
theorem integral_cube_abs_qShell (R : Shell d h) :
    (∫ x, |qShell R x| ∂Haar.cubeMeasure d) = shellVolume h := by
  unfold qShell Haar.cubeMeasure
  simp_rw [Finset.abs_prod]
  rw [integral_fintype_prod_eq_prod (fun j x => |qI (R.1.depth j) (R.2 j) x|)]
  simp_rw [integral_unit_abs_qI]
  exact prod_sideLengths R.1

theorem integral_cube_qShell_sq (R : Shell d h) :
    (∫ x, qShell R x ^ 2 ∂Haar.cubeMeasure d) = shellVolume h := by
  unfold qShell Haar.cubeMeasure
  simp_rw [← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (fun j x => qI (R.1.depth j) (R.2 j) x ^ 2)]
  simp_rw [integral_unit_qI_sq]
  exact prod_sideLengths R.1

/-- The normalization constant gamma_d=192^(-d) is explicit. -/
def gamma (d : ℕ) : ℝ := ((192 : ℝ) ^ d)⁻¹

theorem gamma_pos (d : ℕ) : 0 < gamma d := by unfold gamma; positivity

/-- Exact squared integral of the actual unnormalized tensor primitive. -/
theorem integral_cube_psiShell_sq (R : Shell d h) :
    (∫ x, psiShell R x ^ 2 ∂Haar.cubeMeasure d) = gamma d * shellVolume h ^ 3 := by
  unfold psiShell Haar.cubeMeasure
  simp_rw [← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (fun j x => psiI (R.1.depth j) (R.2 j) x ^ 2)]
  have hi (j : Fin d) : (∫ x, psiI (R.1.depth j) (R.2 j) x ^ 2 ∂Haar.unitMeasure) =
      dyadicLength (R.1.depth j) ^ 3 / 192 := by
    rw [Haar.integral_unitMeasure]
    exact integral_unit_psiI_sq _ _
  simp_rw [hi]
  rw [Finset.prod_div_distrib, Finset.prod_pow, prod_sideLengths]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold gamma
  ring

/-- Actual tensor-product inner product, before applying geometry. -/
theorem integral_cube_psiShell_mul_factor (R S : Shell d h) :
    (∫ x, psiShell R x * psiShell S x ∂Haar.cubeMeasure d) =
      ∏ j, ∫ x in (0 : ℝ)..1,
        psiI (R.1.depth j) (R.2 j) x * psiI (S.1.depth j) (S.2 j) x := by
  unfold psiShell Haar.cubeMeasure
  simp_rw [← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun j x =>
    psiI (R.1.depth j) (R.2 j) x * psiI (S.1.depth j) (S.2 j) x)]
  apply Finset.prod_congr rfl
  intro j _
  exact Haar.integral_unitMeasure _

/-- Distinct shells have orthogonal actual primitives. -/
theorem integral_cube_psiShell_mul_of_ne (R S : Shell d h) (hRS : R ≠ S) :
    (∫ x, psiShell R x * psiShell S x ∂Haar.cubeMeasure d) = 0 := by
  classical
  rw [integral_cube_psiShell_mul_factor]
  rcases R with ⟨r, c⟩
  rcases S with ⟨s, c'⟩
  by_cases hrs : r = s
  · subst s
    have hcc : c ≠ c' := fun h => hRS (by subst c'; rfl)
    have hj : ∃ j, c j ≠ c' j := by
      by_contra! h
      exact hcc (funext h)
    obtain ⟨j, hj⟩ := hj
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact integral_psiI_mul_psiI_same_depth _ _ _ hj
  · have hj : ∃ j, r.depth j ≠ s.depth j := by
      by_contra! h
      exact hrs (Shape.ext (funext h))
    obtain ⟨j, hj⟩ := hj
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rcases lt_or_gt_of_ne hj with hlt | hlt
    · exact integral_psiI_mul_psiI_separated _ _ (depth_separation r s j hlt) _ _
    · simpa only [mul_comm] using
        integral_psiI_mul_psiI_separated _ _ (depth_separation s r j hlt) (c' j) (c j)

/-- Exact normalization of the diagonal inner product. -/
theorem integral_cube_normalizedPrimitive_sq (R : Shell d h) :
    (∫ x, normalizedPrimitive R x ^ 2 ∂Haar.cubeMeasure d) = gamma d * shellVolume h := by
  have heq (x : Point d) : normalizedPrimitive R x ^ 2 =
      (shellVolume h)⁻¹ ^ 2 * psiShell R x ^ 2 := by simp only [normalizedPrimitive, mul_pow]
  simp_rw [heq]
  rw [integral_const_mul, integral_cube_psiShell_sq]
  field_simp [(shellVolume_pos h).ne']

/-- Main.pdf Lemma 3.1, for the concrete primitives and actual cube measure. -/
theorem normalizedPrimitive_orthogonality (R S : Shell d h) :
    (∫ x, normalizedPrimitive R x * normalizedPrimitive S x ∂Haar.cubeMeasure d) =
      if R = S then gamma d * shellVolume h else 0 := by
  classical
  by_cases hRS : R = S
  · subst S
    simpa only [if_pos rfl, pow_two] using integral_cube_normalizedPrimitive_sq R
  · rw [if_neg hRS]
    have heq (x : Point d) : normalizedPrimitive R x * normalizedPrimitive S x =
        (shellVolume h)⁻¹ ^ 2 * (psiShell R x * psiShell S x) := by
      unfold normalizedPrimitive
      ring
    simp_rw [heq]
    rw [integral_const_mul, integral_cube_psiShell_mul_of_ne R S hRS, mul_zero]

end Tusnady.Witness
