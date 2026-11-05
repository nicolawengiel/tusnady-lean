import Tusnady.CellDeficits

/-! # Proved geometric bounds on every retained primitive component. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.DyadicFunctions Tusnady.Haar
open scoped BigOperators

lemma dyadicLength_mul_pow (j : ℕ) : dyadicLength j*(2:ℝ)^j = 1 := by
  unfold dyadicLength
  field_simp

lemma dyadicLength_add (a b : ℕ) : dyadicLength (a+b) = dyadicLength a*dyadicLength b := by
  unfold dyadicLength
  rw [pow_add]
  ring

lemma dyadicLength_mul_pow_sub (j b : ℕ) (hb : b ≤ j) :
    dyadicLength j*(2:ℝ)^(j-b) = dyadicLength b := by
  have hp : (2:ℝ)^j = (2:ℝ)^b*(2:ℝ)^(j-b) := by
    rw [← pow_add, Nat.add_sub_of_le hb]
  unfold dyadicLength
  rw [hp]
  field_simp

lemma factorPrimitiveMass_nonneg {H : ℕ} (f : Factor H) : 0 ≤ factorPrimitiveMass f := by
  cases f with
  | constant c => unfold factorPrimitiveMass; positivity
  | haar a i c => have hl := dyadicLength_pos a.val; unfold factorPrimitiveMass; positivity
  | walsh a ha i c => have hl := dyadicLength_pos a; unfold factorPrimitiveMass; positivity

lemma ancestorSigns_sq (j : ℕ) (i : Fin (2^j)) (b : Fin j) : ancestorSigns j i b^2 = 1 := by
  rcases ancestorSigns_are_signs j i b with h | h <;> rw [h] <;> norm_num

/-- The actual plain Haar-component norm simplifies to the exact dyadic
length expression; its sign has square one by the proved expansion. -/
lemma componentMass_plain_haar (H j : ℕ) (hj : j+2 < H) (i : Fin (2^j)) (b : Fin j) :
    factorPrimitiveMass (componentFactor H j hj i false (some b)) =
      dyadicLength j^2*dyadicLength b.val/12 := by
  change (ancestorSigns j i b*dyadicLength j*(2:ℝ)^b.val)^2*dyadicLength b.val^3/12 = _
  calc
    _ = ancestorSigns j i b^2*dyadicLength j^2*dyadicLength b.val*
        (dyadicLength b.val*(2:ℝ)^b.val)^2/12 := by ring
    _ = _ := by rw [ancestorSigns_sq, dyadicLength_mul_pow]; ring

/-- Uniform coordinate estimate in terms of the **computed** deficit.
No component-norm bound is assumed. -/
theorem componentMass_le_deficit (H j : ℕ) (hj : j+2 < H) (i : Fin (2^j))
    (m : Bool) (b : ComponentIndex j m) :
    factorPrimitiveMass (componentFactor H j hj i m b) ≤
      dyadicLength j^3*(2:ℝ)^(componentDeficit j m b) := by
  have hl := dyadicLength_pos j
  cases m with
  | true =>
    change (1:ℝ)^2*dyadicLength j^3/192 ≤ dyadicLength j^3*(2:ℝ)^0
    norm_num
    nlinarith [pow_nonneg hl.le 3]
  | false =>
    cases b with
    | none =>
      change dyadicLength j^2/3 ≤ dyadicLength j^3*(2:ℝ)^(j+1)
      have heq : dyadicLength j^3*(2:ℝ)^(j+1) = 2*dyadicLength j^2 := by
        rw [pow_succ]
        calc
          _ = dyadicLength j^2*(dyadicLength j*(2:ℝ)^j)*2 := by ring
          _ = _ := by rw [dyadicLength_mul_pow]; ring
      rw [heq]
      nlinarith [sq_nonneg (dyadicLength j)]
    | some b =>
      rw [componentMass_plain_haar]
      change dyadicLength j^2*dyadicLength b.val/12 ≤ dyadicLength j^3*(2:ℝ)^(j-b.val)
      have heq : dyadicLength j^3*(2:ℝ)^(j-b.val) = dyadicLength j^2*dyadicLength b.val := by
        calc
          _ = dyadicLength j^2*(dyadicLength j*(2:ℝ)^(j-b.val)) := by ring
          _ = _ := by rw [dyadicLength_mul_pow_sub j b.val b.isLt.le]
      rw [heq]
      have hnonneg := mul_nonneg (sq_nonneg (dyadicLength j)) (dyadicLength_pos b.val).le
      nlinarith

lemma prod_dyadicLength {d : ℕ} (j : Fin d → ℕ) :
    (∏ k, dyadicLength (j k)) = dyadicLength (∑ k, j k) := by
  unfold dyadicLength
  rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow_eq_pow_sum]

/-- Product bound before imposing the high-level cutoff. -/
theorem componentMass_product_le_deficit {d H : ℕ} (j : Fin d → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool)
    (b : ComponentChoices j m) :
    (∏ k, factorPrimitiveMass (cellComponentFactors j hj I m b k)) ≤
      dyadicLength (∑ k, j k)^3*(2:ℝ)^(componentDeficitSum j m b) := by
  calc
    _ ≤ ∏ k, dyadicLength (j k)^3*(2:ℝ)^(componentDeficit (j k) (m k) (b k)) := by
      apply Finset.prod_le_prod
      · intro k _
        exact factorPrimitiveMass_nonneg _
      · intro k _
        exact componentMass_le_deficit H (j k) (hj k) (I k) (m k) (b k)
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow, prod_dyadicLength,
        Finset.prod_pow_eq_pow_sum]
      rfl

/-- Exact dyadic rescaling of the component bound into shell/excess form. -/
lemma componentBound_rescale (d h e : ℕ) :
    dyadicLength (h+e)^3*(2:ℝ)^(e+2*d) =
      (2:ℝ)^(2*d)*dyadicLength h^3*dyadicLength e^2 := by
  rw [dyadicLength_add, mul_pow, pow_add]
  calc
    _ = (2:ℝ)^(2*d)*dyadicLength h^3*dyadicLength e^2*
        (dyadicLength e*(2:ℝ)^e) := by ring
    _ = _ := by rw [dyadicLength_mul_pow]; ring

/-- The manuscript's uniform retained-component bound, with its explicit
constant 2^(2d), derived from actual primitive norms and actual retention. -/
theorem retained_componentMass_le {d H : ℕ} (h e : ℕ) (j : Fin d → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool)
    (hjoin : ∑ k, j k = h+e) (b : ComponentChoices j m)
    (hb : b ∈ retainedComponents h j hj I m) :
    (∏ k, factorPrimitiveMass (cellComponentFactors j hj I m b k)) ≤
      (2:ℝ)^(2*d)*dyadicLength h^3*dyadicLength e^2 := by
  have hdef := retained_deficit_sum_le h e j hj I m hjoin b hb
  have hp : (2:ℝ)^(componentDeficitSum j m b) ≤ (2:ℝ)^(e+2*d) :=
    pow_le_pow_right₀ (by norm_num) hdef
  calc
    _ ≤ dyadicLength (∑ k, j k)^3*(2:ℝ)^(componentDeficitSum j m b) :=
      componentMass_product_le_deficit j hj I m b
    _ = dyadicLength (h+e)^3*(2:ℝ)^(componentDeficitSum j m b) := by rw [hjoin]
    _ ≤ dyadicLength (h+e)^3*(2:ℝ)^(e+2*d) :=
      mul_le_mul_of_nonneg_left hp (pow_nonneg (dyadicLength_pos (h+e)).le 3)
    _ = _ := componentBound_rescale d h e

end Tusnady.Cell
