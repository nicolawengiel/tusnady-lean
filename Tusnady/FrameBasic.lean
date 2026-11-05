import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! Actual finite real frame energies and elementary trace/rank facts.
There is no assumed frame-selection or spectral-partition theorem. -/

noncomputable section
open Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.Frame

abbrev Space (D : ℕ) := EuclideanSpace ℝ (Fin D)

def energy {D M : ℕ} (v : Fin M → Space D) (S : Finset (Fin M)) (w : Space D) : ℝ :=
  ∑ j ∈ S, inner ℝ w (v j) ^ 2

def Tight {D M : ℕ} (v : Fin M → Space D) : Prop :=
  ∀ w, energy v Finset.univ w = ‖w‖ ^ 2

lemma energy_nonneg {D M : ℕ} (v : Fin M → Space D) (S : Finset (Fin M)) (w : Space D) :
    0 ≤ energy v S w := Finset.sum_nonneg fun j _ => sq_nonneg _

theorem tight_trace {D M : ℕ} (v : Fin M → Space D) (hv : Tight v) :
    ∑ j, ‖v j‖ ^ 2 = (D : ℝ) := by
  classical
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_comm]
  have hi (i : Fin D) : ∑ j, (v j i) ^ 2 = 1 := by
    have he := hv (EuclideanSpace.single i 1)
    simpa [energy, EuclideanSpace.inner_single_left] using he
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

theorem tight_vector_norm_sq_le_one {D M : ℕ} (v : Fin M → Space D) (hv : Tight v)
    (j : Fin M) : ‖v j‖ ^ 2 ≤ 1 := by
  have hs := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
    sq_nonneg (inner ℝ (v j) (v k))) (Finset.mem_univ j)
  have ht := hv (v j)
  change (∑ k, inner ℝ (v j) (v k) ^ 2) = ‖v j‖ ^ 2 at ht
  rw [ht, real_inner_self_eq_norm_sq] at hs
  nlinarith [sq_nonneg (‖v j‖ ^ 2 - 1)]

theorem tight_dimension_le_count {D M : ℕ} (v : Fin M → Space D) (hv : Tight v) : D ≤ M := by
  let T : Space D →ₗ[ℝ] (Fin M → ℝ) := {
    toFun := fun w j => inner ℝ (v j) w
    map_add' := by intro x y; ext j; exact inner_add_right _ _ _
    map_smul' := by intro c x; ext j; simp [inner_smul_right] }
  have hker : ∀ w, T w = 0 → w = 0 := by
    intro w hw
    have he := hv w
    have hz (j : Fin M) : inner ℝ w (v j) = 0 := by
      rw [real_inner_comm]
      exact congrFun hw j
    simp only [energy, hz, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at he
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
  have hinj : Function.Injective T := by
    intro w z hwz
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hwz, sub_self]
  have he := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Space] using he

/-- Lower bounds for either part follow algebraically from the actual
tight-frame identity and upper bounds for its complement. -/
theorem partition_lower_from_upper {D M : ℕ} (v : Fin M → Space D) (hv : Tight v)
    (S : Finset (Fin M)) (b : ℝ)
    (hcomp : ∀ w, energy v (Finset.univ \ S) w ≤ b * ‖w‖ ^ 2) (w : Space D) :
    (1 - b) * ‖w‖ ^ 2 ≤ energy v S w := by
  classical
  have he : energy v S w + energy v (Finset.univ \ S) w = ‖w‖ ^ 2 := by
    rw [← hv w]
    unfold energy
    exact Finset.sum_add_sum_compl S _
  nlinarith [hcomp w]

end Tusnady.Frame
