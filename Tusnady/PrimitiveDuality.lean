import Tusnady.TestFunctionIntegrals
import Tusnady.HaarPrimitiveCongruence

/-!
# Actual anchored-discrepancy duality for W

Finite point weights pair with the actual primitive of W. The L1 bound
then controls the pairing by the actual weighted anchored-box discrepancy.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace Tusnady

variable {d : ℕ} {ι : Type*} [Fintype ι]

def upperOrthant (p : Point d) : Set (Point d) := {x | p ∈ Anchored x}

lemma measurableSet_upperOrthant (p : Point d) : MeasurableSet (upperOrthant p) := by
  have heq : upperOrthant p = ⋂ j : Fin d, {x : Point d | p j ≤ x j} := by
    ext x
    simp [upperOrthant, Anchored]
  rw [heq]
  exact MeasurableSet.iInter fun j => measurableSet_le measurable_const (measurable_pi_apply j)

/-- Actual weighted anchored count, over precisely the trace from Definitions. -/
def weightedAnchoredCount (P : ι → Point d) (z : ι → ℝ) (x : Point d) : ℝ :=
  ∑ i ∈ trace P x, z i

lemma weightedAnchoredCount_eq_indicators (P : ι → Point d) (z : ι → ℝ) (x : Point d) :
    weightedAnchoredCount P z x =
      ∑ i, (upperOrthant (P i)).indicator (fun _ => z i) x := by
  classical
  simp [weightedAnchoredCount, trace, upperOrthant, Set.indicator_apply, Finset.sum_filter]

lemma upperOrthant_iff_upperBox (p x : Point d) (hx : x ∈ UnitCube d) :
    x ∈ upperOrthant p ↔ x ∈ upperBox p := by
  constructor
  · intro hp j _
    exact ⟨hp j, (hx j).2⟩
  · intro hp j
    exact (hp j (Set.mem_univ j)).1

lemma boxPrimitive_eq_integral_upperOrthant (f : Point d → ℝ) (p : Point d)
    (hp : p ∈ UnitCube d) :
    boxPrimitive f p = ∫ x, (upperOrthant p).indicator f x ∂Haar.cubeMeasure d := by
  rw [Haar.boxPrimitive_eq_integral_cubeMeasure f p hp,
    ← integral_indicator (upperBox_measurable p)]
  apply integral_congr_ae
  filter_upwards [Haar.cubeMeasure_ae_UnitCube d] with x hx
  by_cases h : x ∈ upperOrthant p
  · simp only [Set.indicator_of_mem h,
      Set.indicator_of_mem ((upperOrthant_iff_upperBox p x hx).mp h)]
  · simp only [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (mt (upperOrthant_iff_upperBox p x hx).mpr h)]

/-- Exact finite point/primitive duality with the manuscript's closed
anchored boxes. All finite-integral interchanges are justified. -/
theorem weighted_primitive_duality (P : ι → Point d) (hP : ∀ i, P i ∈ UnitCube d)
    (z : ι → ℝ) (f : Point d → ℝ) (hf : Integrable f (Haar.cubeMeasure d)) :
    (∑ i, z i * boxPrimitive f (P i)) =
      ∫ x, weightedAnchoredCount P z x * f x ∂Haar.cubeMeasure d := by
  classical
  have heq : (fun x => weightedAnchoredCount P z x * f x) =
      (fun x => ∑ i, z i * (upperOrthant (P i)).indicator f x) := by
    funext x
    rw [weightedAnchoredCount_eq_indicators, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ upperOrthant (P i) <;> simp [hx]
  rw [heq, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, boxPrimitive_eq_integral_upperOrthant f (P i) (hP i)]
  · intro i _
    exact (hf.indicator (measurableSet_upperOrthant (P i))).const_mul _

lemma weightedAnchoredCount_mul_integrable (P : ι → Point d) (z : ι → ℝ)
    (f : Point d → ℝ) (hf : Integrable f (Haar.cubeMeasure d)) :
    Integrable (fun x => weightedAnchoredCount P z x * f x) (Haar.cubeMeasure d) := by
  classical
  have heq : (fun x => weightedAnchoredCount P z x * f x) =
      (fun x => ∑ i, z i * (upperOrthant (P i)).indicator f x) := by
    funext x
    rw [weightedAnchoredCount_eq_indicators, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ upperOrthant (P i) <;> simp [hx]
  rw [heq]
  exact integrable_finset_sum _ fun i _ =>
    (hf.indicator (measurableSet_upperOrthant (P i))).const_mul _

/-- Actual L1 duality bound for arbitrary point weights. -/
theorem weighted_primitive_abs_le (P : ι → Point d) (hP : ∀ i, P i ∈ UnitCube d)
    (z : ι → ℝ) (f : Point d → ℝ) (hf : Integrable f (Haar.cubeMeasure d))
    (t : ℝ) (ht : 0 ≤ t)
    (hcount : ∀ x ∈ UnitCube d, |weightedAnchoredCount P z x| ≤ t)
    (hL1 : (∫ x, |f x| ∂Haar.cubeMeasure d) ≤ 1) :
    |∑ i, z i * boxPrimitive f (P i)| ≤ t := by
  have hprod := weightedAnchoredCount_mul_integrable P z f hf
  rw [weighted_primitive_duality P hP z f hf]
  calc
    _ ≤ ∫ x, |weightedAnchoredCount P z x * f x| ∂Haar.cubeMeasure d :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, t*|f x| ∂Haar.cubeMeasure d := by
      apply integral_mono_ae hprod.abs (hf.abs.const_mul t)
      filter_upwards [Haar.cubeMeasure_ae_UnitCube d] with x hx
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcount x hx) (abs_nonneg _)
    _ = t*(∫ x, |f x| ∂Haar.cubeMeasure d) := integral_const_mul _ _
    _ ≤ t*1 := mul_le_mul_of_nonneg_left hL1 ht
    _ = t := mul_one t

/-- The actual manuscript test function supplies the duality input for
all coefficient vectors in its cube, with no L1/duality assumption. -/
theorem testFunction_weighted_duality {n : ℕ} (j : Fin (n+1)) (theta : ℝ)
    (u : Witness.Shell (n+1) h → ℝ) (hu : ∀ R, |u R| ≤ 1)
    (P : ι → Point (n+1)) (hP : ∀ i, P i ∈ UnitCube (n+1))
    (z : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hcount : ∀ x ∈ UnitCube (n+1), |weightedAnchoredCount P z x| ≤ t) :
    |∑ i, z i * boxPrimitive (Witness.testFunction j theta u) (P i)| ≤ t := by
  exact weighted_primitive_abs_le P hP z _
    (Witness.integrable_testFunction j theta u hu) t ht hcount
    (Witness.integral_abs_testFunction_le_one j theta u hu)

end Tusnady
