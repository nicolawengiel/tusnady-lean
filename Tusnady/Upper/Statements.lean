import Tusnady.Definitions
import Mathlib.Tactic

/-!
# Exact target statements for Nikolov's upper bound

These propositions specify the new goal; their definitions do not prove
Nikolov's theorem. The equivalences below are proved directly from the
unchanged discrepancy definitions. In the coloring statement a single
coloring precedes every orthant, including when N = 0.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady

/-- Regularized natural-logarithm growth, defined also for zero points. -/
def upperGrowth (d N : ℕ) : ℝ :=
  Real.rpow (Real.log (2 + (N : ℝ))) ((d : ℝ) - (1 / 2 : ℝ))

/-- The exact all-N upper-bound goal, not a proof of that goal. -/
def HigherDimensionalUpperBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, worstDiscrepancy d N ≤ C * upperGrowth d N

/-- One coloring simultaneously controls all closed lower orthants.
The constant is chosen before N and before the point configuration. -/
def ColoringUpperBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∀ P : Fin N → Point d, Function.Injective P →
      ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
        ∀ x : Point d, |realAnchoredCount P χ x| ≤ C * upperGrowth d N

/-- The usual asymptotic log N upper-bound goal. -/
def AsymptoticUpperBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → worstDiscrepancy d N ≤ C * targetGrowth d N

/-- The sharp two-sided growth statement in dimensions at least three. -/
def SharpHigherDimensionalOrder : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * targetGrowth d N ≤ worstDiscrepancy d N ∧
        worstDiscrepancy d N ≤ C * targetGrowth d N

variable {ι : Type*} [Fintype ι] {d : ℕ}

/-- All realizable incidence patterns are controlled by the same coloring. -/
theorem coloringDiscrepancy_le_iff (P : ι → Point d) (χ : ι → Bool) (a : ℝ) :
    coloringDiscrepancy P χ ≤ a ↔ ∀ x : Point d, |anchoredCount P χ x| ≤ a := by
  classical
  constructor
  · intro h x
    exact (Finset.le_sup' (fun S => |signedSum χ S|) (trace_mem_traces P x)).trans h
  · intro h
    apply Finset.sup'_le
    intro S hS
    obtain ⟨x, rfl⟩ := (mem_traces_iff P S).mp hS
    exact h x

/-- Taking the finite minimum is equivalent to the existence of one
coloring that works for every orthant. -/
theorem pointDiscrepancy_le_iff (P : ι → Point d) (a : ℝ) :
    pointDiscrepancy P ≤ a ↔
      ∃ χ : ι → Bool, ∀ x : Point d, |anchoredCount P χ x| ≤ a := by
  classical
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := exists_minimizing_coloring P
    exact ⟨χ, (coloringDiscrepancy_le_iff P χ a).mp (hχ ▸ h)⟩
  · rintro ⟨χ, hχ⟩
    exact (Finset.inf'_le (coloringDiscrepancy P) (Finset.mem_univ χ)).trans
      ((coloringDiscrepancy_le_iff P χ a).mpr hχ)

/-- The existential coloring can equivalently be represented by real ±1 values. -/
theorem pointDiscrepancy_le_iff_real_colorings (P : ι → Point d) (a : ℝ) :
    pointDiscrepancy P ≤ a ↔
      ∃ χ : ι → ℝ, IsSignColoring χ ∧
        ∀ x : Point d, |realAnchoredCount P χ x| ≤ a := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (pointDiscrepancy_le_iff P a).mp h
    exact ⟨fun i => sign (b i), fun i => sign_is_sign (b i), hb⟩
  · rintro ⟨χ, hχ, h⟩
    obtain ⟨b, hb⟩ := coloring_exhaustive χ hχ
    apply (pointDiscrepancy_le_iff P a).mpr
    refine ⟨b, fun x => ?_⟩
    have heq : anchoredCount P b x = realAnchoredCount P χ x := by
      unfold anchoredCount signedSum realAnchoredCount
      exact Finset.sum_congr rfl (fun i _ => hb i)
    simpa only [heq] using h x

/-- A uniform upper bound on worst discrepancy controls every configuration. -/
theorem worstDiscrepancy_le_iff (hd : 0 < d) (N : ℕ) (a : ℝ) :
    worstDiscrepancy d N ≤ a ↔
      ∀ P : Fin N → Point d, Function.Injective P → pointDiscrepancy P ≤ a := by
  constructor
  · intro h P hP
    exact (pointDiscrepancy_le_worst P hP).trans h
  · intro h
    obtain ⟨P, hP, heq⟩ := exists_worst_configuration hd N
    exact heq ▸ h P hP

/-- Fixed constants have exactly the same force in both upper formulations. -/
theorem worstDiscrepancy_le_iff_real_colorings (hd : 0 < d) (N : ℕ) (a : ℝ) :
    worstDiscrepancy d N ≤ a ↔
      ∀ P : Fin N → Point d, Function.Injective P →
        ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
          ∀ x : Point d, |realAnchoredCount P χ x| ≤ a := by
  rw [worstDiscrepancy_le_iff hd N a]
  exact forall_congr' fun P => forall_congr' fun _ =>
    pointDiscrepancy_le_iff_real_colorings P a

theorem upper_iff_coloringUpperBound : HigherDimensionalUpperBound ↔ ColoringUpperBound := by
  constructor
  · intro h d hd
    obtain ⟨C, hC, h⟩ := h d hd
    exact ⟨C, hC, fun N => (worstDiscrepancy_le_iff_real_colorings (by omega) N _).mp (h N)⟩
  · intro h d hd
    obtain ⟨C, hC, h⟩ := h d hd
    exact ⟨C, hC, fun N => (worstDiscrepancy_le_iff_real_colorings (by omega) N _).mpr (h N)⟩

/-- The elementary cardinality bound is uniform over configurations. -/
theorem worstDiscrepancy_le_card (hd : 0 < d) (N : ℕ) :
    worstDiscrepancy d N ≤ (N : ℝ) := by
  apply (worstDiscrepancy_le_iff hd N _).mpr
  intro P _
  simpa only [Fintype.card_fin] using pointDiscrepancy_le_card P

/-- Worst discrepancy is nonnegative in every positive dimension. -/
theorem worstDiscrepancy_nonneg (hd : 0 < d) (N : ℕ) :
    0 ≤ worstDiscrepancy d N := by
  obtain ⟨P, _, hP⟩ := exists_worst_configuration hd N
  rw [← hP]
  exact pointDiscrepancy_nonneg P

/-- Empty point configurations have exactly zero discrepancy. -/
theorem worstDiscrepancy_zero (hd : 0 < d) : worstDiscrepancy d 0 = 0 := by
  obtain ⟨P, _, hP⟩ := exists_worst_configuration hd 0
  rw [← hP]
  exact le_antisymm (by simpa using pointDiscrepancy_le_card P) (pointDiscrepancy_nonneg P)

lemma upperGrowth_pos (d N : ℕ) : 0 < upperGrowth d N := by
  apply Real.rpow_pos_of_pos
  apply Real.log_pos
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

lemma upperGrowth_nonneg (d N : ℕ) : 0 ≤ upperGrowth d N := (upperGrowth_pos d N).le

end Tusnady
