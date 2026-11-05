import Tusnady.TestFunction
import Tusnady.WalshOddExtension
import Tusnady.StepBlock

/-!
# Actual coordinate slices of the manuscript blocks

On each parent interval a block equals its three-bit Walsh sign times
one bounded coefficient. All equalities hold at the dyadic endpoints
with the half-open convention used in the manuscript.
-/
noncomputable section
open scoped BigOperators
open Set
namespace Tusnady.Witness
open Tusnady.Dyadic Tusnady.DyadicFunctions

lemma qI_left (a : ℕ) (i : Fin (2^a)) : qI a i (dyadicLeft a i) = 1 := by
  change qBase ((dyadicLeft a i-dyadicLeft a i)/dyadicLength a) = 1
  rw [sub_self, zero_div]
  exact qBase_on_cell 0 0 (by norm_num [baseCell, cellLo, cellHi])

lemma left_mem_interval (a : ℕ) (i : Fin (2^a)) :
    dyadicLeft a i ∈ dyadicInterval a i := by
  constructor
  · exact le_rfl
  · exact lt_add_of_pos_right _ (dyadicLength_pos a)

lemma qI_compare_on_interval (a : ℕ) (i k : Fin (2^a)) {t : ℝ}
    (ht : t ∈ dyadicInterval a i) :
    qI a k t = qI a i t * qI a k (dyadicLeft a i) := by
  classical
  by_cases hki : k = i
  · subst k
    rw [qI_left, mul_one]
  · have ht' : t ∉ dyadicInterval a k := fun hk =>
      Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a k i hki) hk ht
    have hl' : dyadicLeft a i ∉ dyadicInterval a k := fun hk =>
      Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a k i hki) hk
        (left_mem_interval a i)
    rw [qI_zero_outside _ _ _ ht', qI_zero_outside _ _ _ hl', mul_zero]

lemma qShell_update_split (R : Shell d h) (j : Fin d) (x : Point d) (t : ℝ) :
    qShell R (Function.update x j t) = qI (R.1.depth j) (R.2 j) t *
      ∏ k ∈ (Finset.univ : Finset (Fin d)).erase j,
        qI (R.1.depth k) (R.2 k) (x k) := by
  classical
  unfold qShell
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]

lemma layer_slice (r : Shape d h) (j : Fin d) (a : ℕ)
    (ha : r.depth j = a) (i : Fin (2^a)) (u : Shell d h → ℝ)
    (x : Point d) {t : ℝ} (ht : t ∈ dyadicInterval a i) :
    layer r u (Function.update x j t) =
      qI a i t * layer r u (Function.update x j (dyadicLeft a i)) := by
  subst a
  unfold layer
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [qShell_update_split, qShell_update_split,
    qI_compare_on_interval _ i (c j) ht]
  ring

/-- Exact slice identity for the actual nonlinear block. -/
theorem block_slice (j : Fin d) (a : BlockIndex h) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) (i : Fin (2^a.val.val))
    {t : ℝ} (ht : t ∈ dyadicInterval a.val.val i) :
    block j a theta u (Function.update x j t) =
      qI a.val.val i t * block j a theta u
        (Function.update x j (dyadicLeft a.val.val i)) := by
  unfold block
  have hy : (fun r : ShapesInBlock j a => layer r.val u (Function.update x j t)) =
      (fun r : ShapesInBlock j a => qI a.val.val i t *
        layer r.val u (Function.update x j (dyadicLeft a.val.val i))) := by
    funext r
    exact layer_slice r.val j a.val.val r.property i u x ht
  rw [hy]
  apply Walsh.extension_sign_of_odd (Walsh.smoothedBlock_odd theta)
  change |q (dyadicLeft a.val.val i) (dyadicLength a.val.val) t| = 1
  rw [abs_q _ _ _ (dyadicLength_pos _)]
  exact Set.indicator_of_mem ht _

/-- The actual coefficients of the step representation, with no choice
of representatives or omitted boundary values. -/
def sliceCoefficients (j : Fin d) (a : BlockIndex h) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) (i : Fin (2^a.val.val)) : ℝ :=
  block j a theta u (Function.update x j (dyadicLeft a.val.val i))

theorem sliceCoefficients_bound (j : Fin d) (a : BlockIndex h) (theta : ℝ)
    (u : Shell d h → ℝ) (hu : ∀ R, |u R| ≤ 1) (x : Point d)
    (i : Fin (2^a.val.val)) : |sliceCoefficients j a theta u x i| ≤ 1 :=
  abs_block_le_one j a theta u hu _

theorem block_slice_eq_stepBlock (j : Fin d) (a : BlockIndex h) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) {t : ℝ} (ht : t ∈ Ico (0:ℝ) 1) :
    block j a theta u (Function.update x j t) =
      stepBlock a.val.val (sliceCoefficients j a theta u x) t := by
  obtain ⟨i, hi, _⟩ := Tusnady.Haar.existsUnique_unit_interval a.val.val t ht
  rw [block_slice j a theta u x i hi,
    stepBlock_on_interval _ _ i hi]
  exact mul_comm _ _

end Tusnady.Witness
