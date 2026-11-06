import Tusnady.Boxes.Definitions
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Finite closed realizations of strict thresholds

Every strict lower cutoff in the inclusion-exclusion formula can be replaced
by a closed threshold on the finite indexed input. This includes empty input,
repeated coordinates and a coordinate equal to either corner of the box.
-/
noncomputable section
namespace Tusnady.Boxes

variable {ι : Type*} [Fintype ι] {d : ℕ}

theorem exists_closed_strict_threshold (f : ι → ℝ) (a : ℝ) :
    ∃ c : ℝ, c < a ∧ ∀ i, f i ≤ c ↔ f i < a := by
  classical
  let S : Finset ℝ := insert (a - 1) ((Finset.univ.filter (fun i => f i < a)).image f)
  have hS : S.Nonempty := ⟨a - 1, Finset.mem_insert_self _ _⟩
  refine ⟨S.max' hS, ?_, ?_⟩
  · apply (Finset.max'_lt_iff S hS).mpr
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · linarith
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hi).2
  · intro i
    constructor
    · intro hi
      have hmax : S.max' hS < a := by
        apply (Finset.max'_lt_iff S hS).mpr
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · linarith
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
          exact (Finset.mem_filter.mp hj).2
      exact hi.trans_lt hmax
    · intro hi
      apply Finset.le_max'
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, by simp [hi], rfl⟩)

def strictThreshold (f : ι → ℝ) (a : ℝ) : ℝ :=
  Classical.choose (exists_closed_strict_threshold f a)

theorem strictThreshold_lt (f : ι → ℝ) (a : ℝ) : strictThreshold f a < a :=
  (Classical.choose_spec (exists_closed_strict_threshold f a)).1

theorem le_strictThreshold_iff (f : ι → ℝ) (a : ℝ) (i : ι) :
    f i ≤ strictThreshold f a ↔ f i < a :=
  (Classical.choose_spec (exists_closed_strict_threshold f a)).2 i

/-- A closed orthant with this lower corner realizes a prescribed orthant
trace as a bounded, valid closed box on the finite input. -/
def orthantLower (P : ι → Point d) (x : Point d) (j : Fin d) : ℝ := by
  classical
  exact (insert (x j) (Finset.univ.image (fun i => P i j))).min'
    ⟨x j, Finset.mem_insert_self _ _⟩ - 1

theorem orthantLower_le_upper (P : ι → Point d) (x : Point d) (j : Fin d) :
    orthantLower P x j ≤ x j := by
  classical
  have h := Finset.min'_le (insert (x j) (Finset.univ.image (fun i => P i j)))
    (x j) (Finset.mem_insert_self _ _)
  dsimp [orthantLower]
  linarith

theorem orthantLower_le_point (P : ι → Point d) (x : Point d) (i : ι) (j : Fin d) :
    orthantLower P x j ≤ P i j := by
  classical
  have hi : P i j ∈ insert (x j) (Finset.univ.image (fun i => P i j)) := by simp
  have h := Finset.min'_le (insert (x j) (Finset.univ.image (fun i => P i j))) (P i j) hi
  dsimp [orthantLower]
  linarith

def orthantQuery (P : ι → Point d) (x : Point d) : Query d :=
  ⟨orthantLower P x, x, orthantLower_le_upper P x⟩

theorem mem_orthantQuery_iff (P : ι → Point d) (x : Point d) (i : ι) :
    P i ∈ (orthantQuery P x).region ↔ P i ∈ Anchored x := by
  constructor
  · intro h j
    exact (h j).2
  · intro h j
    exact ⟨orthantLower_le_point P x i j, h j⟩

theorem trace_orthantQuery (P : ι → Point d) (x : Point d) :
    trace P (orthantQuery P x) = Tusnady.trace P x := by
  classical
  ext i
  simp only [trace, Tusnady.trace, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_orthantQuery_iff P x i

theorem orthant_traces_subset (P : ι → Point d) : Tusnady.traces P ⊆ traces P := by
  intro S hS
  obtain ⟨x, rfl⟩ := (Tusnady.mem_traces_iff P S).mp hS
  exact (mem_traces_iff P _).mpr ⟨orthantQuery P x, trace_orthantQuery P x⟩

end Tusnady.Boxes
