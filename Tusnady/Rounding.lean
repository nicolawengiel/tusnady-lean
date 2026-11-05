import Tusnady.MatrixDiscrepancy
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Hereditary discrepancy rounding

Own dyadic-rounding proof of Main.pdf Lemma 2.1. No rounding theorem is
postulated as a literature assumption.
-/

noncomputable section
open scoped BigOperators NNReal
open Filter
namespace Tusnady.Rounding
open MatrixDiscrepancy

def binaryVector {n : ℕ} (b : Fin n → Bool) : Fin n → ℝ :=
  fun j => if b j then 1 else 0

def dyadicPoint {n : ℕ} (k : ℕ) (a : Fin n → ℕ) : Fin n → ℝ :=
  fun j => (a j : ℝ) / (2 : ℝ) ^ k

def halveNumerator (a : ℕ) (up : Bool) : ℕ :=
  a / 2 + if a % 2 = 1 ∧ up = true then 1 else 0

theorem halveNumerator_le (a q : ℕ) (ha : a ≤ 2 * q) (up : Bool) :
    halveNumerator a up ≤ q := by
  unfold halveNumerator
  split <;> omega

theorem halveNumerator_identity (a : ℕ) (up : Bool) :
    2 * (halveNumerator a up : ℝ) - (a : ℝ) =
      if a % 2 = 1 then (if up then 1 else -1) else 0 := by
  have hmod := Nat.mod_lt a (by omega : 0 < 2)
  have hdiv := Nat.mod_add_div a 2
  have hdivR : ((a % 2 : ℕ) : ℝ) + 2 * ((a / 2 : ℕ) : ℝ) = (a : ℝ) := by
    exact_mod_cast hdiv
  have hrem : a % 2 = 0 ∨ a % 2 = 1 := by omega
  rcases hrem with hr | hr <;> cases up
  all_goals simp [halveNumerator, hr] at hdivR ⊢
  all_goals linarith

/-- Dyadic rounding with the exact accumulated geometric-series loss. -/
theorem dyadic_rounding {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hbound : HereditaryBound A D) (k : ℕ) (a : Fin n → ℕ)
    (ha : ∀ j, a j ≤ 2 ^ k) :
    ∃ b : Fin n → Bool, ∀ i : Fin m,
      |∑ j, A i j * (dyadicPoint k a j - binaryVector b j)| ≤
        D * (1 - 1 / (2 : ℝ) ^ k) := by
  classical
  induction k generalizing a with
  | zero =>
    refine ⟨fun j => decide (a j = 1), ?_⟩
    intro i
    have hvec : ∀ j, dyadicPoint 0 a j = binaryVector (fun j => decide (a j = 1)) j := by
      intro j
      have haj := ha j
      simp only [pow_zero] at haj
      have hcases : a j = 0 ∨ a j = 1 := by omega
      rcases hcases with h | h <;> simp [dyadicPoint, binaryVector, h]
    simp [hvec]
  | succ k ih =>
    let S : Finset (Fin n) := Finset.univ.filter (fun j => a j % 2 = 1)
    obtain ⟨σ, hσ⟩ := hbound.2 S
    let a' : Fin n → ℕ := fun j => halveNumerator (a j) (σ j)
    have ha' : ∀ j, a' j ≤ 2 ^ k := by
      intro j
      apply halveNumerator_le
      simpa [pow_succ, Nat.mul_comm] using ha j
    obtain ⟨b, hb⟩ := ih a' ha'
    refine ⟨b, ?_⟩
    intro i
    have hden : (2 : ℝ) ^ (k + 1) ≠ 0 := by positivity
    have hden' : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hpoint : ∀ j,
        dyadicPoint (k + 1) a j - dyadicPoint k a' j =
          -(if j ∈ S then GaussianCover.signVector σ j else 0) / (2 : ℝ) ^ (k + 1) := by
      intro j
      have hj := halveNumerator_identity (a j) (σ j)
      have hS : j ∈ S ↔ a j % 2 = 1 := by simp [S]
      simp only [hS, GaussianCover.signVector] at ⊢
      dsimp [dyadicPoint, a']
      rw [pow_succ]
      field_simp
      nlinarith [hj]
    have herr : (∑ j, A i j * (dyadicPoint (k + 1) a j - dyadicPoint k a' j)) =
        -(signedSum A S σ i) / (2 : ℝ) ^ (k + 1) := by
      have hf : (∑ j : Fin n, if j ∈ S then A i j * GaussianCover.signVector σ j else 0) =
          signedSum A S σ i := by simp [signedSum]
      simp_rw [hpoint, ← mul_div_assoc, mul_neg, mul_ite, mul_zero]
      rw [← Finset.sum_div, Finset.sum_neg_distrib, hf]

    have herr_le : |∑ j, A i j * (dyadicPoint (k + 1) a j - dyadicPoint k a' j)| ≤
        D / (2 : ℝ) ^ (k + 1) := by
      rw [herr, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (k + 1))]
      exact div_le_div_of_nonneg_right (hσ i) (by positivity)
    have hsplit : (∑ j, A i j * (dyadicPoint (k + 1) a j - binaryVector b j)) =
        (∑ j, A i j * (dyadicPoint k a' j - binaryVector b j)) +
        (∑ j, A i j * (dyadicPoint (k + 1) a j - dyadicPoint k a' j)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsplit]
    calc
      _ ≤ |∑ j, A i j * (dyadicPoint k a' j - binaryVector b j)| +
          |∑ j, A i j * (dyadicPoint (k + 1) a j - dyadicPoint k a' j)| := abs_add_le _ _
      _ ≤ D * (1 - 1 / (2 : ℝ) ^ k) + D / (2 : ℝ) ^ (k + 1) :=
        add_le_add (hb i) herr_le
      _ = D * (1 - 1 / (2 : ℝ) ^ (k + 1)) := by
        rw [pow_succ]
        field_simp
        ring

def floorNumerator {n : ℕ} (k : ℕ) (y : Fin n → ℝ) : Fin n → ℕ :=
  fun j => ⌊y j * (2 : ℝ) ^ k⌋₊

theorem floorNumerator_le {n : ℕ} (k : ℕ) (y : Fin n → ℝ)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    ∀ j, floorNumerator k y j ≤ 2 ^ k := by
  intro j
  have hj : ((floorNumerator k y j : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    apply (Nat.floor_le (mul_nonneg (hy j).1 (by positivity))).trans
    exact mul_le_of_le_one_left (by positivity) (hy j).2
  exact_mod_cast hj

theorem dyadicPoint_floor_tendsto {n : ℕ} (y : Fin n → ℝ)
    (hy : ∀ j, 0 ≤ y j) :
    Filter.Tendsto (fun k => dyadicPoint k (floorNumerator k y))
      Filter.atTop (nhds y) := by
  apply tendsto_pi_nhds.mpr
  intro j
  exact (tendsto_nat_floor_mul_div_atTop (hy j)).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

/-- Main.pdf Lemma 2.1 for arbitrary real points of `[0,1]^n`.
The passage from dyadic points uses a proved limit and closedness of the
finite union of rounding events, not an extra approximation assumption. -/
theorem rounding {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hbound : HereditaryBound A D) (y : Fin n → ℝ)
    (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    ∃ b : Fin n → Bool, ∀ i : Fin m,
      |∑ j, A i j * (y j - binaryVector b j)| ≤ D := by
  classical
  let T : Set (Fin n → ℝ) := ⋃ b : Fin n → Bool,
    {z | ∀ i : Fin m, |∑ j, A i j * (z j - binaryVector b j)| ≤ D}
  have hclosed : IsClosed T := by
    apply isClosed_iUnion_of_finite
    intro b
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le (by fun_prop) continuous_const
  have hmem : ∀ k, dyadicPoint k (floorNumerator k y) ∈ T := by
    intro k
    obtain ⟨b, hb⟩ := dyadic_rounding A D hbound k (floorNumerator k y)
      (floorNumerator_le k y hy)
    apply Set.mem_iUnion.mpr
    refine ⟨b, ?_⟩
    intro i
    apply (hb i).trans
    exact mul_le_of_le_one_right hbound.1 (sub_le_self _ (by positivity))
  have hlim : y ∈ T := hclosed.mem_of_tendsto
    (dyadicPoint_floor_tendsto y (fun j => (hy j).1)) (Filter.Eventually.of_forall hmem)
  exact Set.mem_iUnion.mp hlim

/-- The first assertion of Lemma 2.1 from the actual numerical
hereditary discrepancy, with every column subset included. -/
theorem rounding_of_hereditary_le {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) (hD : hereditary A ≤ D)
    (y : Fin n → ℝ) (hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1) :
    ∃ b : Fin n → Bool, ∀ i : Fin m,
      |∑ j, A i j * (y j - binaryVector b j)| ≤ D :=
  rounding A D ((hereditary_le_iff A D).mp hD) y hy

/-- The consequence `(2.1)` in Main.pdf, in the exact event language
used by the Gaussian-cover proof. -/
theorem rounding_cover {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ)
    (hD : hereditary A ≤ D) :
    GaussianCover.cube n 1 ⊆ ⋃ σ : Fin n → Bool,
      GaussianCover.translatedEvent A.mulVecLin D σ := by
  classical
  intro x hx
  let y : Fin n → ℝ := fun j => (x j + 1) / 2
  have hy : ∀ j, 0 ≤ y j ∧ y j ≤ 1 := by
    intro j
    have hj := abs_le.mp (hx j)
    dsimp [y]
    constructor <;> linarith
  obtain ⟨b, hb⟩ := rounding_of_hereditary_le A D hD y hy
  refine Set.mem_iUnion.mpr ⟨b, ?_⟩
  change ∀ i : Fin m,
    |A.mulVec x i - A.mulVec (GaussianCover.signVector b) i| ≤ 2 * D
  intro i
  have heq : A.mulVec x i - A.mulVec (GaussianCover.signVector b) i =
      2 * ∑ j, A i j * (y j - binaryVector b j) := by
    simp only [Matrix.mulVec, dotProduct, ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hs : GaussianCover.signVector b j = 2 * binaryVector b j - 1 := by
      cases hj : b j <;> norm_num [GaussianCover.signVector, binaryVector, hj]
    rw [hs]
    dsimp [y]
    ring
  rw [heq, abs_mul]
  norm_num
  nlinarith [hb i]

/-- Gaussian-cover conclusion with the hereditary-discrepancy rounding
hypothesis discharged by the own proof above. The remaining scalar
Gaussian marginal comparison is explicitly displayed. -/
theorem gaussian_cover_of_marginals {m n : ℕ}
    (hSidak : Literature.Sidak) (hAnderson : Literature.Anderson)
    (μ : MeasureTheory.Measure (Fin n → ℝ))
    (hGaussian : Literature.CenteredGaussian n μ)
    (A : Matrix (Fin m) (Fin n) ℝ) (D : ℝ) (hD : hereditary A ≤ D)
    (hmarginal : ∀ i : Fin n,
      GaussianCover.standardUnitMass ≤ μ {x | |x i| ≤ 1}) :
    (GaussianCover.standardUnitMass / 2) ^ n ≤
      μ (GaussianCover.centeredEvent A.mulVecLin D) :=
  GaussianCover.center_mass_lower_standard_of_cover hSidak hAnderson μ hGaussian
    A.mulVecLin D (rounding_cover A D hD) hmarginal

end Tusnady.Rounding
