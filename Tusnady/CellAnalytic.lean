import Tusnady.CellLinear
import Tusnady.TestFunctionIntegrals
import Tusnady.HaarPrimitiveCongruence

/-! Actual analytic data of the finite cell expansion. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace Tusnady.Witness
variable {d h : ℕ} {j : Fin d}

lemma abs_qShell_le_one (R : Shell d h) (x : Point d) : |qShell R x| ≤ 1 := by
  rw [abs_qShell]
  by_cases hx : x ∈ shellBox R <;> simp [hx]

lemma cellFunction_measurable (S : Finset (BlockShape j h)) (c : CellChoice S) :
    Measurable (cellFunction S c) :=
  Finset.measurable_prod _ fun R _ => measurable_qShell R

lemma abs_cellFunction_le_one (S : Finset (BlockShape j h)) (c : CellChoice S) (x : Point d) :
    |cellFunction S c x| ≤ 1 := by
  unfold cellFunction
  rw [Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun R _ => abs_qShell_le_one R x)

lemma cellFunction_memLp (S : Finset (BlockShape j h)) (c : CellChoice S) :
    MemLp (cellFunction S c) 2 (Haar.cubeMeasure d) := by
  apply MemLp.of_bound (cellFunction_measurable S c).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact abs_cellFunction_le_one S c x

lemma cellFunction_integrable_upperBox (S : Finset (BlockShape j h)) (c : CellChoice S)
    (p : Point d) (hp : p ∈ UnitCube d) :
    IntegrableOn (cellFunction S c) (upperBox p) := by
  rw [IntegrableOn, ← Haar.cubeMeasure_restrict_upperBox p hp]
  exact ((cellFunction_memLp S c).integrable (by norm_num)).restrict

lemma cellMonomial_continuous (S : Finset (BlockShape j h)) (c : CellChoice S) :
    Continuous (cellMonomial S c) := by
  unfold cellMonomial
  exact continuous_finset_prod _ fun R _ => continuous_apply R

/-- The actual primitive of W is the same finite cell polynomial with
actual primitive coefficients, at EVERY sampling point in the cube. -/
theorem boxPrimitive_testFunction_cellExpansion (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (p : Point d) (hp : p ∈ UnitCube d) :
    boxPrimitive (testFunction j theta u) p =
      ∑ S : Finset (BlockShape j h), ∑ c : CellChoice S,
        shapeCoefficient j theta S * cellMonomial S c u * boxPrimitive (cellFunction S c) p := by
  classical
  have heq : testFunction j theta u = fun x => ∑ S : Finset (BlockShape j h),
      ∑ c : CellChoice S, (shapeCoefficient j theta S * cellMonomial S c u) * cellFunction S c x := by
    funext x
    exact testFunction_cellExpansion j theta u x
  rw [heq, boxPrimitive_sum]
  · apply Finset.sum_congr rfl
    intro S _
    rw [boxPrimitive_sum]
    · apply Finset.sum_congr rfl
      intro c _
      exact boxPrimitive_const_mul _ _ _
    · intro c _
      exact (cellFunction_integrable_upperBox S c p hp).const_mul _
  · intro S _
    exact integrable_finset_sum _ fun c _ =>
      (cellFunction_integrable_upperBox S c p hp).const_mul _

/-- The coefficient dependence needed for the actual entropy obstruction
is proved for W's primitive; it is not assumed as an abstract response fact. -/
theorem continuous_primitive_coefficients (j : Fin d) (theta : ℝ)
    (p : Point d) (hp : p ∈ UnitCube d) :
    Continuous (fun u : Shell d h → ℝ => boxPrimitive (testFunction j theta u) p) := by
  have heq : (fun u : Shell d h → ℝ => boxPrimitive (testFunction j theta u) p) =
      (fun u => ∑ S : Finset (BlockShape j h), ∑ c : CellChoice S,
        shapeCoefficient j theta S * cellMonomial S c u * boxPrimitive (cellFunction S c) p) := by
    funext u
    exact boxPrimitive_testFunction_cellExpansion j theta u p hp
  rw [heq]
  apply continuous_finset_sum
  intro S _
  apply continuous_finset_sum
  intro c _
  exact (continuous_const.mul (cellMonomial_continuous S c)).mul continuous_const

end Tusnady.Witness
