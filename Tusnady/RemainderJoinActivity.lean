import Tusnady.RemainderShapeActivity
import Tusnady.RemainderCounting

/-! # Actual join-restricted shape activity

The allowed sets are the actual shapes lying below a depth vector.
Deficit counting is applied to these actual sets and block fibers.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
attribute [local instance] Classical.propDecidable
open Tusnady.RemainderActivity Tusnady.RemainderCounting

def allowedShapeSet (p : Fin d) (j : Fin d → ℕ) : Finset (BlockShape p h) :=
  Finset.univ.filter (fun r => ∀ i, r.2.val.depth i ≤ j i)

theorem card_allowedShapeSet_le (k h e : ℕ) (p : Fin (k + 1))
    (j : Fin (k + 1) → ℕ) (hj : ∑ i, j i = h + e) :
    (allowedShapeSet (h := h) p j).card ≤ (e + 1) ^ k := by
  let f : (allowedShapeSet (h := h) p j) → Dyadic.ShapesBelow (h := h) j :=
    fun r => ⟨r.val.2.val, (Finset.mem_filter.mp r.property).2⟩
  have hf : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    exact (blockShapeEquiv p).injective (congrArg Subtype.val hrs)
  have hc := Fintype.card_le_of_injective f hf
  have hbound := card_shapesBelow_le k h e j hj
  exact (show (allowedShapeSet (h := h) p j).card ≤
    Fintype.card (Dyadic.ShapesBelow (h := h) j) by simpa only [Fintype.card_coe] using hc).trans hbound

theorem card_allowedShapeSet_fiber_le (k h e : ℕ) (p : Fin (k + 2))
    (j : Fin (k + 2) → ℕ) (hj : ∑ i, j i = h + e)
    (a : BlockIndex h) (ha : a.val.val = j p) :
    (FiniteBlocks.fiber (allowedShapeSet (h := h) p j) a).card ≤ (e + 1) ^ k := by
  let E := FiniteBlocks.fiber (allowedShapeSet (h := h) p j) a
  let f : E → {r : Dyadic.ShapesBelow (h := h) j // r.val.depth p = j p} := fun r =>
    ⟨⟨r.val.val, by
      have hmem : (⟨a,r.val⟩ : BlockShape p h) ∈ allowedShapeSet p j := by
        exact (Finset.mem_filter.mp r.property).2
      exact (Finset.mem_filter.mp hmem).2⟩, r.val.property.trans ha⟩
  have hf : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) hrs
  have hc := Fintype.card_le_of_injective f hf
  have hbound := card_shapesBelow_fixed_coordinate_le k h e j hj p
  exact (show E.card ≤ Fintype.card {r : Dyadic.ShapesBelow (h := h) j // r.val.depth p = j p} by
    simpa only [Fintype.card_coe] using hc).trans hbound

theorem shape_classII_join_activity_bound (k h e : ℕ) (p : Fin (k + 1))
    (j : Fin (k + 1) → ℕ) (hj : ∑ i, j i = h + e)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    (∑ S : Finset (BlockShape p h), if S ⊆ allowedShapeSet p j ∧
        3 ≤ (activeBlocks p S).card then shapeCoefficient p theta S ^ 2 else 0) ≤
      (((1 / 4 : ℝ) ^ 2 * theta ^ 2) ^ 3 * (e + 1 : ℕ) ^ (3 * k) / 6) *
        Real.exp ((1 / 4 : ℝ) ^ 2 * theta ^ 2 * (e + 1 : ℕ) ^ k) := by
  have hact := shape_classII_activity_bound p htheta (allowedShapeSet (h := h) p j)
  have hc : ((allowedShapeSet (h := h) p j).card : ℝ) ≤ (e + 1 : ℕ) ^ k := by
    exact_mod_cast card_allowedShapeSet_le k h e p j hj
  have hco : 0 ≤ (1 / 4 : ℝ) ^ 2 * theta ^ 2 := by positivity
  have hz := mul_le_mul_of_nonneg_left hc hco
  calc
    _ ≤ _ := hact
    _ ≤ (((1 / 4 : ℝ) ^ 2 * theta ^ 2 * (e + 1 : ℕ) ^ k) ^ 3 / 6) *
        Real.exp ((1 / 4 : ℝ) ^ 2 * theta ^ 2 * (e + 1 : ℕ) ^ k) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hz 3) (by norm_num)
      · exact Real.exp_le_exp.mpr hz
      · exact Real.exp_nonneg _
      · positivity
    _ = _ := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 3]

theorem shape_classI_join_activity_bound (k h e : ℕ) (p : Fin (k + 2))
    (j : Fin (k + 2) → ℕ) (hj : ∑ i, j i = h + e)
    (a : BlockIndex h) (ha : a.val.val = j p)
    {theta : ℝ} (htheta : 0 ≤ theta) :
    (∑ T ∈ (Finset.univ : Finset (Finset (ShapesInBlock p a))).filter
      (fun T => T ⊆ FiniteBlocks.fiber (allowedShapeSet (h := h) p j) a ∧ 3 ≤ T.card),
        ((1 / 4 : ℝ) * Walsh.coefficient (Walsh.smoothedBlock theta) T) ^ 2) ≤
      (1 / 4 : ℝ) ^ 2 * theta ^ 6 * (e + 1 : ℕ) ^ (3 * k) := by
  have hact := one_block_third_activity p htheta a (FiniteBlocks.fiber (allowedShapeSet (h := h) p j) a)
  have hc : ((FiniteBlocks.fiber (allowedShapeSet (h := h) p j) a).card : ℝ) ≤ (e + 1 : ℕ) ^ k := by
    exact_mod_cast card_allowedShapeSet_fiber_le k h e p j hj a ha
  calc
    _ ≤ _ := hact
    _ ≤ (1 / 4 : ℝ) ^ 2 * theta ^ 6 * ((e + 1 : ℕ) ^ k : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 3) (by positivity)
    _ = _ := by rw [← pow_mul, Nat.mul_comm k 3]

end Tusnady.Witness
