import Tusnady.CellAnalytic
import Tusnady.UniformMonomial

/-! The actual linear primitive and its exact mean-square size. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace Tusnady.Witness
variable {d h : ℕ}

lemma qShell_memLp (R : Shell d h) : MemLp (qShell R) 2 (Haar.cubeMeasure d) := by
  apply MemLp.of_bound (measurable_qShell R).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact abs_qShell_le_one R x

lemma normalizedPrimitive_memLp (R : Shell d h) :
    MemLp (normalizedPrimitive R) 2 (Haar.cubeMeasure d) := by
  apply (memLp_two_iff_integrable_sq
    (continuous_normalizedPrimitive R).measurable.aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  rw [integral_cube_normalizedPrimitive_sq]
  exact (mul_pos (gamma_pos d) (shellVolume_pos h)).ne'

def linearPrimitiveValue (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) (x : Point d) : ℝ :=
  shellVolume h * ∑ R, (linearCoefficient j theta R * u R) * normalizedPrimitive R x

theorem boxPrimitive_linearTestFunction (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (p : Point d) (hp : p ∈ UnitCube d) :
    boxPrimitive (linearTestFunction j theta u) p = linearPrimitiveValue j theta u p := by
  classical
  unfold linearTestFunction
  rw [boxPrimitive_sum]
  · unfold linearPrimitiveValue
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R _
    rw [boxPrimitive_const_mul, boxPrimitive_qShell_normalized R p hp]
    ring
  · intro R _
    rw [IntegrableOn, ← Haar.cubeMeasure_restrict_upperBox p hp]
    exact (((qShell_memLp R).integrable (by norm_num)).restrict).const_mul _

/-- The actual orthogonal primitive family gives the exact deterministic
squared norm, for every real coefficient vector. -/
theorem integral_sum_normalizedPrimitive_sq (a : Shell d h → ℝ) :
    (∫ x, (∑ R, a R * normalizedPrimitive R x)^2 ∂Haar.cubeMeasure d) =
      gamma d * shellVolume h * ∑ R, a R^2 := by
  classical
  have heq (x : Point d) : (∑ R, a R*normalizedPrimitive R x)^2 =
      ∑ R : Shell d h, ∑ S : Shell d h,
        (a R*a S)*(normalizedPrimitive R x*normalizedPrimitive S x) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro R _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  have hint (R S : Shell d h) : Integrable
      (fun x => (a R*a S)*(normalizedPrimitive R x*normalizedPrimitive S x)) (Haar.cubeMeasure d) :=
    ((normalizedPrimitive_memLp R).integrable_mul (normalizedPrimitive_memLp S)).const_mul _
  simp_rw [heq]
  rw [integral_finset_sum]
  · simp_rw [integral_finset_sum _ (fun S _ => hint _ S), integral_const_mul,
      normalizedPrimitive_orthogonality]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R _
    ring
  · intro R _
    exact integrable_finset_sum _ fun S _ => hint R S

theorem integral_linearPrimitive_sq (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) :
    (∫ x, linearPrimitiveValue j theta u x^2 ∂Haar.cubeMeasure d) =
      gamma d * shellVolume h^3 * ∑ R, linearCoefficient j theta R^2 * u R^2 := by
  unfold linearPrimitiveValue
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sum_normalizedPrimitive_sq]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro R _
  ring

/-- Main.pdf (3.15), exact equality with the actual product-uniform law. -/
theorem expected_linearPrimitive_sq (j : Fin d) (theta : ℝ) :
    (∫ u, (∫ x, linearPrimitiveValue j theta u x^2 ∂Haar.cubeMeasure d)
      ∂UniformMonomial.cubeLaw (Shell d h)) =
      gamma d * shellVolume h^3 / 3 * ∑ R : Shell d h, linearCoefficient j theta R^2 := by
  classical
  have hm (R : Shell d h) :
      (∫ u, u R^2 ∂UniformMonomial.cubeLaw (Shell d h)) = (1/3:ℝ) := by
    simpa only [UniformMonomial.monomial, Finset.prod_singleton, if_pos rfl, ite_true,
      Finset.card_singleton, pow_one, ← pow_two] using
      UniformMonomial.monomial_mixed_moment ({R} : Finset (Shell d h)) {R}
  have hint (R : Shell d h) : Integrable
      (fun u : Shell d h → ℝ => u R^2) (UniformMonomial.cubeLaw (Shell d h)) := by
    simpa only [UniformMonomial.monomial, Finset.prod_singleton, ← pow_two] using
      UniformMonomial.monomial_product_integrable ({R} : Finset (Shell d h)) {R}
  simp_rw [integral_linearPrimitive_sq]
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [integral_const_mul, hm]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro R _
    ring
  · intro R _
    exact (hint R).const_mul _

lemma volume_cube_card_shell (d h : ℕ) :
    shellVolume h^3 * (Fintype.card (Shell d h):ℝ) =
      shellVolume h^2 * (Fintype.card (Dyadic.Shape d h):ℝ) := by
  rw [card_shell]
  push_cast
  unfold shellVolume
  field_simp

/-- Exact quantitative linear-energy bounds before the separate shape
count. The explicit block-size budget is the one in the manuscript. -/
theorem expected_linearPrimitive_bounds (j : Fin d) {theta : ℝ} (htheta : 0 ≤ theta)
    (hbudget : ∀ a : BlockIndex h,
      theta^2*(Fintype.card (ShapesInBlock j a):ℝ) ≤ (1:ℝ)/4) :
    (gamma d/192)*theta^2*(Fintype.card (Dyadic.Shape d h):ℝ)*shellVolume h^2 ≤
      (∫ u, (∫ x, linearPrimitiveValue j theta u x^2 ∂Haar.cubeMeasure d)
        ∂UniformMonomial.cubeLaw (Shell d h)) ∧
    (∫ u, (∫ x, linearPrimitiveValue j theta u x^2 ∂Haar.cubeMeasure d)
      ∂UniformMonomial.cubeLaw (Shell d h)) ≤
      (gamma d/48)*theta^2*(Fintype.card (Dyadic.Shape d h):ℝ)*shellVolume h^2 := by
  classical
  have hlo : (Fintype.card (Shell d h):ℝ)*(theta/8)^2 ≤
      ∑ R : Shell d h, linearCoefficient j theta R^2 := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Shell d h)))
      (f := fun _ => (theta/8)^2) (g := fun R => linearCoefficient j theta R^2)
      (fun R _ => by
        have hR := (linearCoefficient_bounds j htheta hbudget R).1
        nlinarith)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have hhi : (∑ R : Shell d h, linearCoefficient j theta R^2) ≤
      (Fintype.card (Shell d h):ℝ)*(theta/4)^2 := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Shell d h)))
      (f := fun R => linearCoefficient j theta R^2) (g := fun _ => (theta/4)^2)
      (fun R _ => by
        have hR := linearCoefficient_bounds j htheta hbudget R
        nlinarith)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hh
  have hp : 0 ≤ gamma d*shellVolume h^3/3 := by
    have hg := gamma_pos d
    have hv := shellVolume_pos h
    positivity
  rw [expected_linearPrimitive_sq]
  constructor
  · calc
      _ = (gamma d/192*theta^2)*(shellVolume h^3*(Fintype.card (Shell d h):ℝ)) := by
        rw [volume_cube_card_shell]
        ring
      _ = (gamma d*shellVolume h^3/3)*((Fintype.card (Shell d h):ℝ)*(theta/8)^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hp
  · calc
      _ ≤ (gamma d*shellVolume h^3/3)*((Fintype.card (Shell d h):ℝ)*(theta/4)^2) :=
        mul_le_mul_of_nonneg_left hhi hp
      _ = (gamma d/48*theta^2)*(shellVolume h^3*(Fintype.card (Shell d h):ℝ)) := by ring
      _ = _ := by rw [volume_cube_card_shell]; ring

end Tusnady.Witness
