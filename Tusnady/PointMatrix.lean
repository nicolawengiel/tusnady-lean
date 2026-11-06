import Tusnady.Definitions
import Tusnady.MatrixDiscrepancy
import Tusnady.Padding
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

/-! # The actual finite anchored-box incidence matrix

Rows enumerate exactly the realizable traces of closed lower orthants.
Distinct points give an injective incidence operator. No geometric
general-position assumption is used, so tied coordinates are allowed.
-/

noncomputable section
open scoped BigOperators NNReal
namespace Tusnady

def incidenceRow {d n : ℕ} (P : Fin n → Point d)
    (r : Fin (traces P).card) : Finset (Fin n) :=
  ((traces P).equivFin.symm r).val

theorem incidenceRow_mem {d n : ℕ} (P : Fin n → Point d)
    (r : Fin (traces P).card) : incidenceRow P r ∈ traces P :=
  ((traces P).equivFin.symm r).property

theorem incidenceRow_surjective {d n : ℕ} (P : Fin n → Point d)
    (S : Finset (Fin n)) (hS : S ∈ traces P) : ∃ r, incidenceRow P r = S := by
  refine ⟨(traces P).equivFin ⟨S, hS⟩, ?_⟩
  simp [incidenceRow]

def incidenceMatrix {d n : ℕ} (P : Fin n → Point d) :
    Matrix (Fin (traces P).card) (Fin n) ℝ :=
  fun r j => if j ∈ incidenceRow P r then 1 else 0

theorem incidenceMatrix_mulVec {d n : ℕ} (P : Fin n → Point d)
    (r : Fin (traces P).card) (z : Fin n → ℝ) :
    (incidenceMatrix P).mulVec z r = ∑ j ∈ incidenceRow P r, z j := by
  classical
  simp [incidenceMatrix, Matrix.mulVec, dotProduct]

/-- Vanishing of all anchored sums forces every point weight to vanish.
A minimal point of the nonzero support isolates one nonzero coefficient. -/
theorem anchored_sums_separate {d n : ℕ} (P : Fin n → Point d)
    (hP : Function.Injective P) (z : Fin n → ℝ)
    (hz : ∀ x : Point d, (∑ j ∈ trace P x, z j) = 0) : z = 0 := by
  classical
  by_contra hne
  have hex : ∃ i : Fin n, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  let S := Finset.univ.filter (fun i : Fin n => z i ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [S, hi]⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_minimalFor P S hS
  have hzi : z i ≠ 0 := (Finset.mem_filter.mp hi).2
  have hsum : (∑ j ∈ trace P (P i), z j) = z i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      by_contra hzj
      have hjS : j ∈ S := by simp [S, hzj]
      have hle : P j ≤ P i := (Finset.mem_filter.mp hj).2
      have hreverse : P i ≤ P j := hmin hjS hle
      exact hji (hP (le_antisymm hle hreverse))
    · intro hnot
      exact (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => le_rfl⟩)).elim
  exact hzi (hsum.symm.trans (hz (P i)))

theorem incidenceMatrix_injective {d n : ℕ} (P : Fin n → Point d)
    (hP : Function.Injective P) : Function.Injective (incidenceMatrix P).mulVecLin := by
  intro z w hzw
  have hzero : (incidenceMatrix P).mulVecLin (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  have hz : z - w = 0 := anchored_sums_separate P hP (z - w) (by
    intro x
    obtain ⟨r, hr⟩ := incidenceRow_surjective P (trace P x) (trace_mem_traces P x)
    have h := congrFun hzero r
    change (incidenceMatrix P).mulVec (z - w) r = 0 at h
    rwa [incidenceMatrix_mulVec, hr] at h)
  exact sub_eq_zero.mp hz

theorem incidenceMatrix_signedSum {d n : ℕ} (P : Fin n → Point d)
    (S : Finset (Fin n)) (σ : Fin n → Bool) (x : Point d)
    (r : Fin (traces P).card) (hr : incidenceRow P r = trace P x) :
    MatrixDiscrepancy.signedSum (incidenceMatrix P) S σ r =
      anchoredCount (fun j : S => P j) (fun j => σ j) x := by
  classical
  have hsub := Finset.sum_subtype (p := fun j : Fin n => j ∈ S) (F := inferInstance) S (fun j => Iff.rfl)
    (fun j => if P j ∈ Anchored x then sign (σ j) else 0)
  have hlhs : MatrixDiscrepancy.signedSum (incidenceMatrix P) S σ r =
      ∑ j ∈ S, if P j ∈ Anchored x then sign (σ j) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : P j ∈ Anchored x <;>
      simp [incidenceMatrix, hr, trace, hj, GaussianCover.signVector, sign]
  rw [hlhs]
  simpa only [anchoredCount, signedSum, trace, Finset.sum_filter] using hsub

/-- Matrix row supremum and the actual box discrepancy of a restricted
point coloring are identical, including the empty column subset. -/
theorem incidenceMatrix_coloringCost {d n : ℕ} (P : Fin n → Point d)
    (S : Finset (Fin n)) (σ : Fin n → Bool) :
    (MatrixDiscrepancy.coloringCost (incidenceMatrix P) S σ : ℝ) =
      coloringDiscrepancy (fun j : S => P j) (fun j => σ j) := by
  classical
  apply le_antisymm
  · have hn := coloringDiscrepancy_nonneg (fun j : S => P j) (fun j => σ j)
    change (MatrixDiscrepancy.coloringCost (incidenceMatrix P) S σ : ℝ) ≤
      ((⟨coloringDiscrepancy (fun j : S => P j) (fun j => σ j), hn⟩ : ℝ≥0) : ℝ)
    apply NNReal.coe_le_coe.mpr
    apply (MatrixDiscrepancy.coloringCost_le_iff _ _ _ ⟨_, hn⟩).mpr
    intro r
    obtain ⟨x, hx⟩ := (mem_traces_iff P _).mp (incidenceRow_mem P r)
    rw [incidenceMatrix_signedSum P S σ x r hx.symm]
    exact Finset.le_sup' (fun T => |signedSum (fun j : S => σ j) T|)
      (trace_mem_traces (fun j : S => P j) x)
  · apply Finset.sup'_le
    intro T hT
    obtain ⟨x, hx⟩ := (mem_traces_iff (fun j : S => P j) T).mp hT
    obtain ⟨r, hr⟩ := incidenceRow_surjective P (trace P x) (trace_mem_traces P x)
    have hrow := Finset.le_sup (f := fun r =>
      Real.nnabs (MatrixDiscrepancy.signedSum (incidenceMatrix P) S σ r))
      (Finset.mem_univ r)
    have hre := NNReal.coe_le_coe.mpr hrow
    change |MatrixDiscrepancy.signedSum (incidenceMatrix P) S σ r| ≤
      (MatrixDiscrepancy.coloringCost (incidenceMatrix P) S σ : ℝ) at hre
    rw [incidenceMatrix_signedSum P S σ x r hr] at hre
    simpa only [Real.coe_nnabs, anchoredCount, hx] using hre

set_option maxHeartbeats 1000000 in
/-- Exact identification of restricted matrix discrepancy and discrepancy
of the actual indexed point subset. Full colorings are freely extended
from the subset; no balance or auxiliary coloring constraint is imposed. -/
theorem incidenceMatrix_restricted_discrepancy {d n : ℕ} (P : Fin n → Point d)
    (S : Finset (Fin n)) :
    (MatrixDiscrepancy.discrepancyNN (incidenceMatrix P) S : ℝ) =
      pointDiscrepancy (fun j : S => P j) := by
  classical
  apply le_antisymm
  · obtain ⟨σ, hσ⟩ := exists_minimizing_coloring (fun j : S => P j)
    let τ : Fin n → Bool := fun j => if hj : j ∈ S then σ ⟨j, hj⟩ else false
    have hext : (fun j : S => τ j) = σ := by funext j; simp [τ]
    have hmin := Finset.inf'_le (MatrixDiscrepancy.coloringCost (incidenceMatrix P) S)
      (Finset.mem_univ τ)
    have hminreal := NNReal.coe_le_coe.mpr hmin
    change (MatrixDiscrepancy.discrepancyNN (incidenceMatrix P) S : ℝ) ≤ _ at hminreal
    rw [incidenceMatrix_coloringCost, hext, ← hσ] at hminreal
    exact hminreal
  · obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (MatrixDiscrepancy.coloringCost (incidenceMatrix P) S)
    have hmin := Finset.inf'_le (coloringDiscrepancy (fun j : S => P j))
      (Finset.mem_univ (fun j : S => σ j))
    have hmin' : pointDiscrepancy (fun j : S => P j) ≤
        coloringDiscrepancy (fun j : S => P j) (fun j : S => σ j) := by
      unfold pointDiscrepancy
      convert hmin using 1
      congr 1
      ext b
      simp
    clear hmin
    rw [← incidenceMatrix_coloringCost P S σ, ← hσ] at hmin'
    exact hmin'

/-- The hereditary maximum is attained by an actual subset of the point
set. This is the manuscript's `HerdiscPoints` step, with exact equality. -/
theorem incidenceMatrix_hereditary_attained {d n : ℕ} (P : Fin n → Point d) :
    ∃ S : Finset (Fin n), MatrixDiscrepancy.hereditary (incidenceMatrix P) =
      pointDiscrepancy (fun j : S => P j) := by
  classical
  obtain ⟨S, _, hS⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
    (MatrixDiscrepancy.discrepancyNN (incidenceMatrix P))
  refine ⟨S, ?_⟩
  change (MatrixDiscrepancy.hereditaryNN (incidenceMatrix P) : ℝ) = _
  rw [MatrixDiscrepancy.hereditaryNN, hS, incidenceMatrix_restricted_discrepancy]

theorem pointDiscrepancy_reindex {d : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (P : ι → Point d) : pointDiscrepancy (P ∘ e) = pointDiscrepancy P := by
  apply le_antisymm
  · apply (le_pointDiscrepancy_iff P _).mpr
    intro χ
    obtain ⟨x, hx⟩ := (le_pointDiscrepancy_iff (P ∘ e) _).mp le_rfl (χ ∘ e)
    exact ⟨x, (anchoredCount_reindex e P χ x) ▸ hx⟩
  · apply (le_pointDiscrepancy_iff (P ∘ e) _).mpr
    intro χ
    obtain ⟨x, hx⟩ := (le_pointDiscrepancy_iff P _).mp le_rfl (χ ∘ e.symm)
    have heq := anchoredCount_reindex e P (χ ∘ e.symm) x
    have hχ : (χ ∘ e.symm) ∘ e = χ := by funext i; simp
    rw [hχ] at heq
    exact ⟨x, heq.symm ▸ hx⟩

/-- For points in the open unit cube, every real orthant trace already
occurs at a parameter in the closed unit cube. -/
theorem anchoredCount_clamp {d : ℕ} {ι : Type*} [Fintype ι]
    (P : ι → Point d) (hP : ∀ i, P i ∈ OpenUnitCube d)
    (χ : ι → Bool) (x : Point d) :
    anchoredCount P χ (fun j => max 0 (min 1 (x j))) = anchoredCount P χ x := by
  classical
  have hp (i : ι) : P i ∈ Anchored (fun j => max 0 (min 1 (x j))) ↔
      P i ∈ Anchored x := by
    apply forall_congr'
    intro j
    constructor
    · intro h
      rcases le_max_iff.mp h with hz | hm
      · exact ((not_le.mpr (hP i j).1) hz).elim
      · exact hm.trans (min_le_right _ _)
    · intro h
      exact le_max_of_le_right (le_min (hP i j).2.le h)
  simp only [anchoredCount_eq_sum, hp]

theorem clamp_mem_unitCube {d : ℕ} (x : Point d) :
    (fun j => max 0 (min 1 (x j))) ∈ UnitCube d := by
  intro j
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Hereditary discrepancy is attained by a subset represented by exactly
`k ≤ n` distinct points, with the lower bound against every coloring and
an actual witness box parameter in `[0,1]^d`. This directly supplies the
input to `padding_to_exact_cardinality`. -/
theorem incidenceMatrix_hereditary_subset {d n : ℕ} (P : Fin n → Point d)
    (hP : Function.Injective P) (hPc : ∀ i, P i ∈ OpenUnitCube d) :
    ∃ k : ℕ, k ≤ n ∧ ∃ Q : Fin k → Point d,
      Function.Injective Q ∧ (∀ i, Q i ∈ OpenUnitCube d) ∧
      pointDiscrepancy Q = MatrixDiscrepancy.hereditary (incidenceMatrix P) ∧
      ∀ χ : Fin k → Bool, ∃ x : Point d, x ∈ UnitCube d ∧
        MatrixDiscrepancy.hereditary (incidenceMatrix P) ≤ |anchoredCount Q χ x| := by
  classical
  obtain ⟨S, hS⟩ := incidenceMatrix_hereditary_attained P
  let Q : Fin S.card → Point d := fun i => P ((S.equivFin.symm i).val)
  have hQ : ∀ i, Q i ∈ OpenUnitCube d := fun i => hPc _
  have heq : pointDiscrepancy Q = MatrixDiscrepancy.hereditary (incidenceMatrix P) := by
    exact (pointDiscrepancy_reindex S.equivFin.symm (fun j : S => P j)).trans hS.symm
  refine ⟨S.card, by simpa using Finset.card_le_univ S, Q,
    hP.comp (Subtype.val_injective.comp S.equivFin.symm.injective), hQ, heq, ?_⟩
  intro χ
  obtain ⟨x, hx⟩ := (le_pointDiscrepancy_iff Q _).mp heq.ge χ
  refine ⟨fun j => max 0 (min 1 (x j)), clamp_mem_unitCube x, ?_⟩
  rwa [anchoredCount_clamp Q hQ χ x]

theorem incidenceMatrix_hereditary_ge_one {d n : ℕ} (P : Fin n → Point d)
    (hn : 0 < n) (hPc : ∀ i j, P i j ≤ 1) :
    1 ≤ MatrixDiscrepancy.hereditary (incidenceMatrix P) := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hfull : trace P (fun _ => 1) = Finset.univ := by
    ext j
    simp [trace, Anchored, hPc]
  obtain ⟨r, hr⟩ := incidenceRow_surjective P _ (trace_mem_traces P (fun _ => 1))
  have hh := (MatrixDiscrepancy.hereditary_le_iff (incidenceMatrix P)
    (MatrixDiscrepancy.hereditary (incidenceMatrix P))).mp le_rfl
  obtain ⟨σ, hσ⟩ := hh.2 {i}
  have h := hσ r
  cases hsi : σ i <;>
  simpa [MatrixDiscrepancy.signedSum, incidenceMatrix, hr, hfull,
    GaussianCover.signVector, hsi] using h

end Tusnady
