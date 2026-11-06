import Tusnady.Definitions
import Tusnady.Upper.Statements

/-!
# Discrepancy for all closed bounded coordinate boxes

These are new definitions. The original `Tusnady` orthant discrepancy is
unchanged. A query carries its finite real lower and upper corners and the
coordinate inequalities between them. Degenerate intervals are allowed.
The trace family contains exactly the realizable incidences of such queries.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Boxes

structure Query (d : ℕ) where
  lower : Point d
  upper : Point d
  valid : ∀ j, lower j ≤ upper j

def Query.region (q : Query d) : Set (Point d) := Tusnady.Box q.lower q.upper

theorem Query.region_eq_Icc (q : Query d) : q.region = Set.Icc q.lower q.upper := by
  ext p
  simp [Query.region, Tusnady.Box, Set.mem_Icc, Pi.le_def, forall_and]

def Query.zero (d : ℕ) : Query d := ⟨fun _ => 0, fun _ => 0, fun _ => le_rfl⟩

variable {ι : Type*} [Fintype ι] {d : ℕ}

def trace (P : ι → Point d) (q : Query d) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => P i ∈ q.region)

def traces (P : ι → Point d) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (fun S => ∃ q : Query d, trace P q = S)

theorem mem_traces_iff (P : ι → Point d) (S : Finset ι) :
    S ∈ traces P ↔ ∃ q : Query d, trace P q = S := by
  classical
  simp [traces]

theorem trace_mem_traces (P : ι → Point d) (q : Query d) : trace P q ∈ traces P :=
  (mem_traces_iff P _).mpr ⟨q, rfl⟩

theorem traces_nonempty (P : ι → Point d) : (traces P).Nonempty :=
  ⟨trace P (Query.zero d), trace_mem_traces P _⟩

def count (P : ι → Point d) (χ : ι → Bool) (q : Query d) : ℝ :=
  signedSum χ (trace P q)

def realCount (P : ι → Point d) (χ : ι → ℝ) (q : Query d) : ℝ :=
  ∑ i ∈ trace P q, χ i

def coloringDiscrepancy (P : ι → Point d) (χ : ι → Bool) : ℝ :=
  (traces P).sup' (traces_nonempty P) (fun S => |signedSum χ S|)

def pointDiscrepancy (P : ι → Point d) : ℝ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (coloringDiscrepancy P)

theorem coloringDiscrepancy_le_card (P : ι → Point d) (χ : ι → Bool) :
    coloringDiscrepancy P χ ≤ Fintype.card ι := by
  classical
  apply Finset.sup'_le
  intro S _
  calc
    |signedSum χ S| ≤ ∑ i ∈ S, |sign (χ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = (S.card : ℝ) := by simp
    _ ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ S

theorem coloringDiscrepancy_nonneg (P : ι → Point d) (χ : ι → Bool) :
    0 ≤ coloringDiscrepancy P χ :=
  (abs_nonneg (signedSum χ (trace P (Query.zero d)))).trans
    (Finset.le_sup' (fun S => |signedSum χ S|) (trace_mem_traces P _))

theorem pointDiscrepancy_nonneg (P : ι → Point d) : 0 ≤ pointDiscrepancy P := by
  classical
  unfold pointDiscrepancy
  apply Finset.le_inf'
  intro χ _
  exact coloringDiscrepancy_nonneg P χ

theorem pointDiscrepancy_le_card (P : ι → Point d) :
    pointDiscrepancy P ≤ Fintype.card ι := by
  classical
  exact (Finset.inf'_le _ (Finset.mem_univ (fun _ => false))).trans
    (coloringDiscrepancy_le_card P _)

theorem exists_minimizing_coloring (P : ι → Point d) :
    ∃ χ : ι → Bool, pointDiscrepancy P = coloringDiscrepancy P χ := by
  classical
  obtain ⟨χ, _, hχ⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (coloringDiscrepancy P)
  exact ⟨χ, hχ⟩

theorem coloringDiscrepancy_le_iff (P : ι → Point d) (χ : ι → Bool) (B : ℝ) :
    coloringDiscrepancy P χ ≤ B ↔ ∀ q : Query d, |count P χ q| ≤ B := by
  classical
  constructor
  · intro h q
    exact (Finset.le_sup' (fun S => |signedSum χ S|) (trace_mem_traces P q)).trans h
  · intro h
    apply Finset.sup'_le
    intro S hS
    obtain ⟨q, rfl⟩ := (mem_traces_iff P S).mp hS
    exact h q

theorem pointDiscrepancy_le_iff (P : ι → Point d) (B : ℝ) :
    pointDiscrepancy P ≤ B ↔ ∃ χ : ι → Bool, ∀ q : Query d, |count P χ q| ≤ B := by
  classical
  constructor
  · intro h
    obtain ⟨χ, hχ⟩ := exists_minimizing_coloring P
    exact ⟨χ, (coloringDiscrepancy_le_iff P χ B).mp (hχ ▸ h)⟩
  · rintro ⟨χ, hχ⟩
    exact (Finset.inf'_le (coloringDiscrepancy P) (Finset.mem_univ χ)).trans
      ((coloringDiscrepancy_le_iff P χ B).mpr hχ)

theorem pointDiscrepancy_le_iff_real_colorings (P : ι → Point d) (B : ℝ) :
    pointDiscrepancy P ≤ B ↔ ∃ χ : ι → ℝ, IsSignColoring χ ∧
      ∀ q : Query d, |realCount P χ q| ≤ B := by
  constructor
  · intro h
    obtain ⟨b, hb⟩ := (pointDiscrepancy_le_iff P B).mp h
    exact ⟨fun i => sign (b i), fun i => sign_is_sign (b i), hb⟩
  · rintro ⟨χ, hχ, hbound⟩
    obtain ⟨b, hb⟩ := coloring_exhaustive χ hχ
    apply (pointDiscrepancy_le_iff P B).mpr
    refine ⟨b, fun q => ?_⟩
    have heq : count P b q = realCount P χ q := by
      exact Finset.sum_congr rfl (fun i _ => hb i)
    simpa only [heq] using hbound q

def worstDiscrepancy (d N : ℕ) : ℝ :=
  sSup {a : ℝ | ∃ P : Fin N → Point d, Function.Injective P ∧ pointDiscrepancy P = a}

theorem configurations_bddAbove (d N : ℕ) :
    BddAbove {a : ℝ | ∃ P : Fin N → Point d,
      Function.Injective P ∧ pointDiscrepancy P = a} := by
  refine ⟨N, ?_⟩
  rintro a ⟨P, _, rfl⟩
  simpa using pointDiscrepancy_le_card P

theorem pointDiscrepancy_le_worst (P : Fin N → Point d) (hP : Function.Injective P) :
    pointDiscrepancy P ≤ worstDiscrepancy d N :=
  le_csSup (configurations_bddAbove d N) ⟨P, hP, rfl⟩

end Tusnady.Boxes
