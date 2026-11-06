import Tusnady.Upper.GaussianConcentration
import Tusnady.Upper.PrefixBalancing
import Mathlib.Topology.MetricSpace.ProperSpace.Real

/-!
# The Gaussian body in Nikolov's proof

The measure here is the actual product standard Gaussian transported to the
Euclidean normed space.  A finite intersection of row slabs has high Gaussian
mass by a proved union bound.  No independence between the row forms is used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace NNReal ENNReal
namespace Tusnady.Upper

/-- The standard Gaussian on the finite Euclidean space used by the factorization. -/
def euclideanGaussian (k : ℕ) : Measure (EuclideanSpace ℝ (Fin k)) :=
  (Literature.standardGaussian k).map (WithLp.toLp 2)

instance euclideanGaussian_probability (k : ℕ) : IsProbabilityMeasure (euclideanGaussian k) := by
  letI : IsProbabilityMeasure (Literature.standardGaussian k) := by
    unfold Literature.standardGaussian
    infer_instance
  change IsProbabilityMeasure ((Literature.standardGaussian k).map (WithLp.toLp 2))
  infer_instance

lemma gaussianLinearForm_eq_inner {k : ℕ} (u : EuclideanSpace ℝ (Fin k))
    (z : Fin k → ℝ) :
    gaussianLinearForm u z = inner ℝ u (WithLp.toLp 2 z) := by
  simp only [gaussianLinearForm, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Concentration for genuine inner products in the Euclidean Gaussian space. -/
theorem euclideanGaussian_inner_tail {k : ℕ} (u : EuclideanSpace ℝ (Fin k))
    {B R : ℝ} (hB : 0 < B) (hu : ‖u‖ ≤ B) (hR : 0 ≤ R) :
    (euclideanGaussian k).real {z | R < |inner ℝ u z|} ≤
      2 * Real.exp (-R^2/(2*B^2)) := by
  have hm : MeasurableSet {z : EuclideanSpace ℝ (Fin k) | R < |inner ℝ u z|} :=
    measurableSet_lt measurable_const (by fun_prop)
  have heq : (euclideanGaussian k) {z | R < |inner ℝ u z|} =
      (Literature.standardGaussian k) {z | R < |gaussianLinearForm u z|} := by
    rw [euclideanGaussian, Measure.map_apply
      (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).measurable hm]
    congr 1
    ext z
    simp only [mem_preimage, mem_setOf_eq, gaussianLinearForm_eq_inner]
  simpa only [measureReal_def, heq] using gaussian_linearForm_tail u hB hu hR

/-- Simultaneous slab constraints, one for every row of the factorization. -/
def rowSlabs {k : ℕ} {ι : Type*} (U : ι → EuclideanSpace ℝ (Fin k)) (R : ℝ) :
    Set (EuclideanSpace ℝ (Fin k)) := {z | ∀ i, |inner ℝ (U i) z| ≤ R}

lemma rowSlabs_closed {k : ℕ} {ι : Type*}
    (U : ι → EuclideanSpace ℝ (Fin k)) (R : ℝ) : IsClosed (rowSlabs U R) := by
  have heq : rowSlabs U R = ⋂ i, {z | |inner ℝ (U i) z| ≤ R} := by
    ext z
    simp [rowSlabs]
  rw [heq]
  apply isClosed_iInter
  intro i
  exact isClosed_le (by fun_prop) continuous_const

lemma rowSlabs_convex {k : ℕ} {ι : Type*}
    (U : ι → EuclideanSpace ℝ (Fin k)) (R : ℝ) : Convex ℝ (rowSlabs U R) := by
  intro x hx y hy a b ha hb hab i
  rw [inner_add_right, inner_smul_right, inner_smul_right]
  calc
    |a * inner ℝ (U i) x + b * inner ℝ (U i) y| ≤
        |a * inner ℝ (U i) x| + |b * inner ℝ (U i) y| := abs_add_le _ _
    _ = a * |inner ℝ (U i) x| + b * |inner ℝ (U i) y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = R := by rw [← add_mul, hab, one_mul]

lemma rowSlabs_symmetric {k : ℕ} {ι : Type*}
    (U : ι → EuclideanSpace ℝ (Fin k)) (R : ℝ) :
    ∀ z ∈ rowSlabs U R, -z ∈ rowSlabs U R := by
  intro z hz i
  simpa only [inner_neg_right, abs_neg] using hz i

lemma rowSlabs_zero {k : ℕ} {ι : Type*}
    (U : ι → EuclideanSpace ℝ (Fin k)) {R : ℝ} (hR : 0 ≤ R) :
    (0 : EuclideanSpace ℝ (Fin k)) ∈ rowSlabs U R := by
  intro i
  simpa using hR

/-- Finite Gaussian union bound for all the row constraints simultaneously. -/
theorem rowSlabs_mass {k : ℕ} {ι : Type*} [Fintype ι]
    (U : ι → EuclideanSpace ℝ (Fin k)) {B R : ℝ}
    (hB : 0 < B) (hU : ∀ i, ‖U i‖ ≤ B) (hR : 0 ≤ R) :
    1 - (Fintype.card ι : ℝ) * (2 * Real.exp (-R^2/(2*B^2))) ≤
      (euclideanGaussian k).real (rowSlabs U R) := by
  classical
  have heq : (rowSlabs U R)ᶜ = ⋃ i, {z | R < |inner ℝ (U i) z|} := by
    ext z
    simp [rowSlabs, not_forall]
  have hcompl : (euclideanGaussian k).real (rowSlabs U R)ᶜ ≤
      (Fintype.card ι : ℝ) * (2 * Real.exp (-R^2/(2*B^2))) := by
    rw [heq]
    calc
      _ ≤ ∑ i, (euclideanGaussian k).real {z | R < |inner ℝ (U i) z|} :=
        measureReal_iUnion_fintype_le _
      _ ≤ ∑ _i : ι, 2 * Real.exp (-R^2/(2*B^2)) :=
        Finset.sum_le_sum fun i _ => euclideanGaussian_inner_tail (U i) hB (hU i) hR
      _ = _ := by simp
  rw [measureReal_compl (rowSlabs_closed U R).measurableSet] at hcompl
  simp only [probReal_univ] at hcompl
  linarith

end Tusnady.Upper
