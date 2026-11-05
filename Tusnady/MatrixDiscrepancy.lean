import Tusnady.GaussianCover
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.NNReal.Basic

/-!
# Finite matrix discrepancy and hereditary discrepancy

Rows and columns are finite, and colorings take exactly the values -1,+1.
The nonnegative finite supremum includes zero, so matrices with zero rows
have discrepancy zero. Restricted columns are represented by sums over a
finite subset; values of a coloring outside that subset are ignored.
-/

noncomputable section
open scoped BigOperators NNReal
namespace Tusnady.MatrixDiscrepancy

abbrev Coloring (n : ℕ) := Fin n → Bool

def signedSum {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n)) (σ : Coloring n) (i : Fin m) : ℝ :=
  ∑ j ∈ S, A i j * GaussianCover.signVector σ j

def coloringCost {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n)) (σ : Coloring n) : ℝ≥0 :=
  Finset.univ.sup (fun i : Fin m => Real.nnabs (signedSum A S σ i))

/-- Minimum over all genuine two-colorings of the selected columns. -/
def discrepancyNN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n)) : ℝ≥0 :=
  Finset.univ.inf' Finset.univ_nonempty (coloringCost A S)

/-- Maximum of the restricted discrepancies over all column subsets. -/
def hereditaryNN {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ≥0 :=
  Finset.univ.sup (discrepancyNN A)

def discrepancy {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ :=
  discrepancyNN A Finset.univ

def hereditary {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : ℝ := hereditaryNN A

/-- The finite-coloring formulation used by the rounding proof. -/
def HereditaryBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) : Prop :=
  0 ≤ D ∧ ∀ S : Finset (Fin n), ∃ σ : Coloring n, ∀ i : Fin m,
    |signedSum A S σ i| ≤ D

theorem hereditary_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ hereditary A := NNReal.coe_nonneg _

theorem coloringCost_le_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (S : Finset (Fin n)) (σ : Coloring n) (D : ℝ≥0) :
    coloringCost A S σ ≤ D ↔ ∀ i, |signedSum A S σ i| ≤ (D : ℝ) := by
  simp only [coloringCost, Finset.sup_le_iff, Finset.mem_univ, true_implies]
  exact forall_congr' fun i => NNReal.coe_le_coe.symm

theorem hereditary_le_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) :
    hereditary A ≤ D ↔ HereditaryBound A D := by
  constructor
  · intro h
    have hD : 0 ≤ D := (hereditary_nonneg A).trans h
    refine ⟨hD, ?_⟩
    intro S
    have hS : discrepancyNN A S ≤ hereditaryNN A :=
      Finset.le_sup (f := discrepancyNN A) (Finset.mem_univ S)
    obtain ⟨σ, _, hσ⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty (coloringCost A S)
    refine ⟨σ, ?_⟩
    have hcost : coloringCost A S σ ≤ (⟨D, hD⟩ : ℝ≥0) := by
      rw [← hσ]
      exact NNReal.coe_le_coe.mp ((NNReal.coe_le_coe.mpr hS).trans h)
    exact (coloringCost_le_iff A S σ ⟨D, hD⟩).mp hcost
  · rintro ⟨hD, h⟩
    change (hereditaryNN A : ℝ) ≤ D
    suffices hereditaryNN A ≤ (⟨D, hD⟩ : ℝ≥0) from NNReal.coe_le_coe.mpr this
    apply Finset.sup_le
    intro S _
    obtain ⟨σ, hσ⟩ := h S
    exact Finset.inf'_le_of_le (f := coloringCost A S) (Finset.mem_univ σ)
      ((coloringCost_le_iff A S σ ⟨D, hD⟩).mpr hσ)

end Tusnady.MatrixDiscrepancy
