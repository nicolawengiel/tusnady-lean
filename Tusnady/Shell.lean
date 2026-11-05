import Tusnady.DyadicGeometry
import Tusnady.DyadicFunctionsGeometry
import Tusnady.HaarFunctions
import Tusnady.Definitions
import Mathlib.Data.Fintype.OfMap
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Actual shell boxes and their tensor Walsh functions

Every shell is an actual shape together with an actual dyadic interval
index in each coordinate. In particular the finite index sets are
constructed, and their finiteness is not assumed.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Tusnady.Dyadic

/-- A bounded finite code for every coordinate of a shell shape. -/
def shapeCode {d h : ℕ} (r : Shape d h) : Fin d → Fin (h + 1) :=
  fun j => ⟨r.depth j, Nat.lt_succ_of_le (depth_le_shell r j)⟩

theorem shapeCode_injective (d h : ℕ) : Function.Injective (@shapeCode d h) := by
  intro r s hrs
  apply Shape.ext
  funext j
  exact congrArg Fin.val (congrFun hrs j)

instance shapeFintype (d h : ℕ) : Fintype (Shape d h) :=
  Fintype.ofInjective shapeCode (shapeCode_injective d h)

end Tusnady.Dyadic

namespace Tusnady.Witness
open Tusnady.Dyadic Tusnady.DyadicFunctions

/-- An actual shell box, indexed without repeated shapes or side indices. -/
abbrev Shell (d h : ℕ) := (r : Shape d h) × CellIndices r.depth

def shellBox (R : Shell d h) : Set (Point d) :=
  {x | ∀ j, x j ∈ dyadicInterval (R.1.depth j) (R.2 j)}

def halfOpenCube (d : ℕ) : Set (Point d) := {x | ∀ j, x j ∈ Ico (0 : ℝ) 1}

def qShell (R : Shell d h) (x : Point d) : ℝ :=
  ∏ j, qI (R.1.depth j) (R.2 j) (x j)

def psiShell (R : Shell d h) (x : Point d) : ℝ :=
  ∏ j, psiI (R.1.depth j) (R.2 j) (x j)

/-- The manuscript's common shell volume. -/
def shellVolume (h : ℕ) : ℝ := ((2 : ℝ) ^ h)⁻¹

/-- The normalized primitive T_R. -/
def normalizedPrimitive (R : Shell d h) (x : Point d) : ℝ :=
  (shellVolume h)⁻¹ * psiShell R x

theorem card_shell (d h : ℕ) :
    Fintype.card (Shell d h) = Fintype.card (Shape d h) * 2 ^ h := by
  rw [Fintype.card_sigma]
  simp only [card_shellCells, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  norm_cast

theorem shellVolume_pos (h : ℕ) : 0 < shellVolume h := by
  unfold shellVolume
  positivity

theorem shellBox_subset_cube (R : Shell d h) : shellBox R ⊆ halfOpenCube d := by
  intro x hx j
  exact dyadicInterval_subset_unit _ _ (hx j)

/-- Real shell boxes of a fixed shape are pairwise disjoint. -/
theorem shellBox_disjoint_same_shape (r : Shape d h) (c c' : CellIndices r.depth)
    (hcc : c ≠ c') : Disjoint (shellBox ⟨r, c⟩) (shellBox ⟨r, c'⟩) := by
  rw [Set.disjoint_left]
  intro x hx hy
  have hne : ∃ j, c j ≠ c' j := by
    by_contra! h
    exact hcc (funext h)
  obtain ⟨j, hj⟩ := hne
  exact Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth _ _ _ hj) (hx j) (hy j)

/-- Each point of the half-open cube lies in exactly one shell of each shape. -/
theorem existsUnique_shell_of_shape (r : Shape d h) (x : Point d) (hx : x ∈ halfOpenCube d) :
    ∃! c : CellIndices r.depth, x ∈ shellBox ⟨r, c⟩ := by
  classical
  let c : CellIndices r.depth := fun j =>
    Classical.choose (Tusnady.Haar.existsUnique_unit_interval (r.depth j) (x j) (hx j))
  have hc : x ∈ shellBox ⟨r, c⟩ := fun j =>
    (Classical.choose_spec (Tusnady.Haar.existsUnique_unit_interval (r.depth j) (x j) (hx j))).1
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  funext j
  exact (Classical.choose_spec
    (Tusnady.Haar.existsUnique_unit_interval (r.depth j) (x j) (hx j))).2 (c' j) (hc' j)

/-- The concrete tensor Walsh function has absolute value the box indicator. -/
theorem abs_qShell (R : Shell d h) (x : Point d) :
    |qShell R x| = (shellBox R).indicator (fun _ => (1 : ℝ)) x := by
  classical
  unfold qShell
  rw [Finset.abs_prod]
  have hq (j : Fin d) : |qI (R.1.depth j) (R.2 j) (x j)| =
      (dyadicInterval (R.1.depth j) (R.2 j)).indicator (fun _ => (1 : ℝ)) (x j) :=
    abs_q _ _ _ (dyadicLength_pos _)
  simp_rw [hq]
  by_cases hx : x ∈ shellBox R
  · rw [Set.indicator_of_mem hx]
    simp only [Set.indicator_of_mem (hx _), Finset.prod_const_one]
  · rw [Set.indicator_of_notMem hx]
    have hne : ∃ j, x j ∉ dyadicInterval (R.1.depth j) (R.2 j) := by
      by_contra! h
      exact hx h
    obtain ⟨j, hj⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact Set.indicator_of_notMem hj _

theorem qShell_zero_outside (R : Shell d h) (x : Point d) (hx : x ∉ shellBox R) :
    qShell R x = 0 := by
  apply abs_eq_zero.mp
  rw [abs_qShell, Set.indicator_of_notMem hx]

theorem abs_qShell_of_mem (R : Shell d h) (x : Point d) (hx : x ∈ shellBox R) :
    |qShell R x| = 1 := by rw [abs_qShell, Set.indicator_of_mem hx]

/-- Each shape's layer is an actual finite sum over its shell cells. -/
def layer (r : Shape d h) (u : Shell d h → ℝ) (x : Point d) : ℝ :=
  ∑ c : CellIndices r.depth, u ⟨r, c⟩ * qShell ⟨r, c⟩ x

theorem layer_eq_on_cell (r : Shape d h) (u : Shell d h → ℝ) (x : Point d)
    (c : CellIndices r.depth) (hx : x ∈ shellBox ⟨r, c⟩) :
    layer r u x = u ⟨r, c⟩ * qShell ⟨r, c⟩ x := by
  classical
  unfold layer
  rw [Finset.sum_eq_single c]
  · intro c' _ hcc
    have hnot : x ∉ shellBox ⟨r, c'⟩ := by
      intro hx'
      exact Set.disjoint_left.mp (shellBox_disjoint_same_shape r c' c hcc) hx' hx
    rw [qShell_zero_outside _ _ hnot, mul_zero]
  · intro hc
    exact False.elim (hc (Finset.mem_univ c))

/-- Pointwise uniform layer bound, including outside the unit cube. -/
theorem abs_layer_le_one (r : Shape d h) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (x : Point d) : |layer r u x| ≤ 1 := by
  classical
  by_cases hx : x ∈ halfOpenCube d
  · obtain ⟨c, hc, _⟩ := existsUnique_shell_of_shape r x hx
    rw [layer_eq_on_cell r u x c hc, abs_mul, abs_qShell_of_mem _ _ hc, mul_one]
    exact hu _
  · have hn (c : CellIndices r.depth) : x ∉ shellBox ⟨r, c⟩ :=
      fun h => hx (shellBox_subset_cube ⟨r, c⟩ h)
    have hz : layer r u x = 0 := by simp [layer, qShell_zero_outside _ _ (hn _)]
    rw [hz]
    norm_num

end Tusnady.Witness
