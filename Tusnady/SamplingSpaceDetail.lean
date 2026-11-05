import Tusnady.SamplingSpaceAffine
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Actual orthogonal dyadic affine differences

`D₀=V₀` and `D_(j+1)=V_(j+1) ∩ V_jᗮ` are genuine subspaces of L².
Dimensions, nested decomposition and mutual orthogonality are proved from
the concrete V_j spaces, not assumed as a free multiresolution structure.
-/

noncomputable section
open MeasureTheory Set
namespace Tusnady.SamplingSpace

/-- The exact orthogonal differences from Main.pdf §5.1. -/
def detailSpace : ℕ → Submodule ℝ L2Real
  | 0 => l2Space 0
  | j + 1 => (l2Space j)ᗮ ⊓ l2Space (j + 1)

theorem detailSpace_le_level (j : ℕ) : detailSpace j ≤ l2Space j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact inf_le_right

instance detailSpace_finiteDimensional (j : ℕ) : FiniteDimensional ℝ (detailSpace j) :=
  Submodule.finiteDimensional_of_le (detailSpace_le_level j)

theorem detailSpace_zero_finrank : Module.finrank ℝ (detailSpace 0) = 2 := by
  simpa [detailSpace] using l2Space_finrank 0

theorem detailSpace_succ_finrank (j : ℕ) :
    Module.finrank ℝ (detailSpace (j + 1)) = 2 ^ (j + 1) := by
  apply Submodule.finrank_add_inf_finrank_orthogonal' (l2Space_mono (Nat.le_succ j))
  rw [l2Space_finrank, l2Space_finrank]
  simp only [pow_succ]
  ring

/-- The actual coarse space and its actual orthogonal difference recover
the whole fine affine space. -/
theorem l2Space_step_decomposition (j : ℕ) :
    l2Space j ⊔ detailSpace (j + 1) = l2Space (j + 1) :=
  Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection (l2Space_mono (Nat.le_succ j))

/-- Different dyadic levels are genuinely orthogonal in Lebesgue L². -/
theorem detailSpace_inner_zero {i j : ℕ} (hij : i < j)
    (f g : L2Real) (hf : f ∈ detailSpace i) (hg : g ∈ detailSpace j) : inner ℝ f g = 0 := by
  cases j with
  | zero => omega
  | succ j =>
    have hile : i ≤ j := Nat.le_of_lt_succ hij
    have hf' : f ∈ l2Space j := l2Space_mono hile (detailSpace_le_level i hf)
    exact hg.1 f hf'

/-- Finite orthogonal sum as a recursively formed supremum. -/
def detailSum : ℕ → Submodule ℝ L2Real
  | 0 => detailSpace 0
  | j + 1 => detailSum j ⊔ detailSpace (j + 1)

theorem detailSum_eq_level (j : ℕ) : detailSum j = l2Space j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simpa only [detailSum, ih] using l2Space_step_decomposition j

end Tusnady.SamplingSpace
