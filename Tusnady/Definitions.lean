import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Exact finite discrepancy definitions

Manuscript Main.pdf, pp. 1–2 and §2.1. Points live in all of ℝ^d.
Anchored boxes are closed lower orthants, including their boundary.
The finite max/min below avoid any ambiguity about unattained suprema.
No distinctness assumption is hidden in discrepancy; it is explicit in the
set of configurations over which `worstDiscrepancy` takes its supremum.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady

abbrev Point (d : ℕ) := Fin d → ℝ

def Anchored (x : Point d) : Set (Point d) := {p | ∀ j, p j ≤ x j}

def Box (a b : Point d) : Set (Point d) := {p | ∀ j, a j ≤ p j ∧ p j ≤ b j}

def UnitCube (d : ℕ) : Set (Point d) := {p | ∀ j, 0 ≤ p j ∧ p j ≤ 1}

def OpenUnitCube (d : ℕ) : Set (Point d) := {p | ∀ j, 0 < p j ∧ p j < 1}

variable {ι : Type*} [Fintype ι]

/-- `true` is +1 and `false` is -1; every one of the 2^|ι| colorings occurs. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]

@[simp] theorem sign_is_sign (b : Bool) : sign b = -1 ∨ sign b = 1 := by
  cases b <;> simp [sign]

def IsSignColoring (χ : ι → ℝ) : Prop := ∀ i, χ i = -1 ∨ χ i = 1

omit [Fintype ι] in
theorem coloring_exhaustive (χ : ι → ℝ) (hχ : IsSignColoring χ) :
    ∃ b : ι → Bool, ∀ i, sign (b i) = χ i := by
  classical
  refine ⟨fun i => decide (χ i = 1), ?_⟩
  intro i
  rcases hχ i with hi | hi <;> norm_num [hi, sign]

def trace (P : ι → Point d) (x : Point d) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => P i ∈ Anchored x)

/-- All and only the finitely many realizable anchored incidence patterns. -/
def traces (P : ι → Point d) : Finset (Finset ι) := by
  classical
  exact Finset.univ.powerset.filter (fun S => ∃ x : Point d, trace P x = S)

theorem mem_traces_iff (P : ι → Point d) (S : Finset ι) :
    S ∈ traces P ↔ ∃ x : Point d, trace P x = S := by
  classical
  simp [traces]

theorem trace_mem_traces (P : ι → Point d) (x : Point d) : trace P x ∈ traces P :=
  (mem_traces_iff P _).2 ⟨x, rfl⟩

theorem traces_nonempty (P : ι → Point d) : (traces P).Nonempty :=
  ⟨trace P (fun _ => 0), trace_mem_traces P _⟩

def signedSum (χ : ι → Bool) (S : Finset ι) : ℝ := ∑ i ∈ S, sign (χ i)

def anchoredCount (P : ι → Point d) (χ : ι → Bool) (x : Point d) : ℝ :=
  signedSum χ (trace P x)

def coloringDiscrepancy (P : ι → Point d) (χ : ι → Bool) : ℝ :=
  (traces P).sup' (traces_nonempty P) (fun S => |signedSum χ S|)

/-- Minimum over every sign coloring, with no balance restriction. -/
def pointDiscrepancy (P : ι → Point d) : ℝ := by
  classical
  exact Finset.univ.inf' Finset.univ_nonempty (coloringDiscrepancy P)

theorem coloringDiscrepancy_le_card (P : ι → Point d) (χ : ι → Bool) :
    coloringDiscrepancy P χ ≤ Fintype.card ι := by
  classical
  apply Finset.sup'_le
  intro S _
  calc
    |signedSum χ S| ≤ ∑ i ∈ S, |sign (χ i)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ = (S.card : ℝ) := by simp
    _ ≤ Fintype.card ι := by exact_mod_cast Finset.card_le_univ S

theorem coloringDiscrepancy_nonneg (P : ι → Point d) (χ : ι → Bool) :
    0 ≤ coloringDiscrepancy P χ := by
  exact (abs_nonneg (signedSum χ (trace P (fun _ => 0)))).trans
    (Finset.le_sup' (fun S => |signedSum χ S|) (trace_mem_traces P (fun _ => 0)))

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

theorem le_coloringDiscrepancy_iff (P : ι → Point d) (χ : ι → Bool) (a : ℝ) :
    a ≤ coloringDiscrepancy P χ ↔ ∃ x : Point d, a ≤ |anchoredCount P χ x| := by
  classical
  rw [coloringDiscrepancy, Finset.le_sup'_iff]
  constructor
  · rintro ⟨S, hS, ha⟩
    obtain ⟨x, hx⟩ := (mem_traces_iff P S).1 hS
    exact ⟨x, by simpa [anchoredCount, hx] using ha⟩
  · rintro ⟨x, hx⟩
    exact ⟨trace P x, trace_mem_traces P x, hx⟩

theorem le_pointDiscrepancy_iff (P : ι → Point d) (a : ℝ) :
    a ≤ pointDiscrepancy P ↔
      ∀ χ : ι → Bool, ∃ x : Point d, a ≤ |anchoredCount P χ x| := by
  classical
  simp only [pointDiscrepancy, Finset.le_inf'_iff, Finset.mem_univ, true_implies,
    le_coloringDiscrepancy_iff]

/-- Weighted box count for an arbitrary real coloring. -/
def realAnchoredCount (P : ι → Point d) (χ : ι → ℝ) (x : Point d) : ℝ :=
  ∑ i ∈ trace P x, χ i

/-- The optimization is equivalent to quantifying over every real ±1
coloring, not only a selected family of colorings. -/
theorem le_pointDiscrepancy_iff_real_colorings (P : ι → Point d) (a : ℝ) :
    a ≤ pointDiscrepancy P ↔ ∀ χ : ι → ℝ, IsSignColoring χ →
      ∃ x : Point d, a ≤ |realAnchoredCount P χ x| := by
  classical
  constructor
  · intro ha χ hχ
    obtain ⟨b, hb⟩ := coloring_exhaustive χ hχ
    obtain ⟨x, hx⟩ := (le_pointDiscrepancy_iff P a).1 ha b
    refine ⟨x, ?_⟩
    have heq : anchoredCount P b x = realAnchoredCount P χ x := by
      unfold anchoredCount signedSum realAnchoredCount
      exact Finset.sum_congr rfl (fun i _ => hb i)
    rwa [heq] at hx
  · intro h
    apply (le_pointDiscrepancy_iff P a).2
    intro b
    obtain ⟨x, hx⟩ := h (fun i => sign (b i)) (fun i => sign_is_sign (b i))
    exact ⟨x, hx⟩

/-- Attainment of the minimum, useful for checking all quantifiers. -/
theorem exists_minimizing_coloring (P : ι → Point d) :
    ∃ χ : ι → Bool, pointDiscrepancy P = coloringDiscrepancy P χ := by
  classical
  obtain ⟨χ, _, hχ⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty
    (coloringDiscrepancy P)
  exact ⟨χ, hχ⟩

/-- Exact supremum in the manuscript; not an average over point configurations. -/
def worstDiscrepancy (d N : ℕ) : ℝ :=
  sSup {a : ℝ | ∃ P : Fin N → Point d, Function.Injective P ∧ pointDiscrepancy P = a}

theorem configurations_bddAbove (d N : ℕ) :
    BddAbove {a : ℝ | ∃ P : Fin N → Point d,
      Function.Injective P ∧ pointDiscrepancy P = a} := by
  refine ⟨N, ?_⟩
  rintro a ⟨P, _, rfl⟩
  simpa using pointDiscrepancy_le_card P

theorem pointDiscrepancy_le_worst (P : Fin N → Point d) (hP : Function.Injective P) :
    pointDiscrepancy P ≤ worstDiscrepancy d N := by
  exact le_csSup (configurations_bddAbove d N) ⟨P, hP, rfl⟩

/-- Injective indexing is literally a finite set of exactly N distinct points. -/
theorem image_card_eq (P : Fin N → Point d) (hP : Function.Injective P) :
    (Finset.univ.image P).card = N := by
  classical
  rw [Finset.card_image_of_injective _ hP, Finset.card_univ, Fintype.card_fin]

/-- Discrepancy is integer valued even though the geometric coordinates are real. -/
theorem exists_nat_pointDiscrepancy (P : ι → Point d) :
    ∃ k : ℕ, k ≤ Fintype.card ι ∧ pointDiscrepancy P = (k : ℝ) := by
  classical
  obtain ⟨χ, hχ⟩ := exists_minimizing_coloring P
  obtain ⟨S, _, hS⟩ := Finset.exists_mem_eq_sup' (traces_nonempty P)
    (fun S => |signedSum χ S|)
  let z : ℤ := ∑ i ∈ S, if χ i then 1 else -1
  have hz : signedSum χ S = (z : ℝ) := by
    simp [signedSum, z, sign, Int.cast_sum, Int.cast_ite]
  have heq : pointDiscrepancy P = (z.natAbs : ℝ) := by
    rw [hχ, coloringDiscrepancy, hS, hz]
    simp
  refine ⟨z.natAbs, ?_, heq⟩
  exact_mod_cast (heq ▸ pointDiscrepancy_le_card P)

theorem configurations_finite (d N : ℕ) :
    {a : ℝ | ∃ P : Fin N → Point d,
      Function.Injective P ∧ pointDiscrepancy P = a}.Finite := by
  refine ((Finset.range (N + 1)).finite_toSet.image (fun k : ℕ => (k : ℝ))).subset ?_
  rintro a ⟨P, _, rfl⟩
  obtain ⟨k, hk, heq⟩ := exists_nat_pointDiscrepancy P
  refine ⟨k, ?_, heq.symm⟩
  simp only [Finset.mem_coe, Finset.mem_range]
  simpa using Nat.lt_succ_of_le hk

theorem configurations_nonempty (hd : 0 < d) (N : ℕ) :
    {a : ℝ | ∃ P : Fin N → Point d,
      Function.Injective P ∧ pointDiscrepancy P = a}.Nonempty := by
  let P : Fin N → Point d := fun i _ => (i.val : ℝ)
  refine ⟨pointDiscrepancy P, P, ?_, rfl⟩
  intro i j hij
  apply Fin.ext
  have h := congrFun hij (⟨0, hd⟩ : Fin d)
  change (i.val : ℝ) = (j.val : ℝ) at h
  exact_mod_cast h

/-- The worst-case supremum is attained, so its quantifiers do give a single
configuration resisting every coloring. Positive dimension is essential here. -/
theorem exists_worst_configuration (hd : 0 < d) (N : ℕ) :
    ∃ P : Fin N → Point d, Function.Injective P ∧
      pointDiscrepancy P = worstDiscrepancy d N := by
  exact (configurations_nonempty hd N).csSup_mem (configurations_finite d N)

theorem le_worstDiscrepancy_iff (hd : 0 < d) (N : ℕ) (a : ℝ) :
    a ≤ worstDiscrepancy d N ↔
      ∃ P : Fin N → Point d, Function.Injective P ∧
        ∀ χ : Fin N → Bool, ∃ x : Point d, a ≤ |anchoredCount P χ x| := by
  constructor
  · intro h
    obtain ⟨P, hP, heq⟩ := exists_worst_configuration hd N
    exact ⟨P, hP, (le_pointDiscrepancy_iff P a).1 (heq ▸ h)⟩
  · rintro ⟨P, hP, h⟩
    exact ((le_pointDiscrepancy_iff P a).2 h).trans (pointDiscrepancy_le_worst P hP)

/-- Natural logarithm and a real exponent, not natural-number subtraction. -/
def targetGrowth (d N : ℕ) : ℝ :=
  Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ))

/-- EXACT TARGET: Main.pdf, Theorem 1.1, p. 2. This is a proposition, not a proof. -/
def HigherDimensionalLowerBound : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → c * targetGrowth d N ≤ worstDiscrepancy d N

/-- The explicit witness form needed by the proposed proof; not assumed. -/
def WitnessLowerBound : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∃ P : Fin N → Point d,
      Function.Injective P ∧ ∀ χ : Fin N → Bool,
        ∃ x : Point d, c * targetGrowth d N ≤ |anchoredCount P χ x|

theorem witnessLowerBound_implies_target (h : WitnessLowerBound) :
    HigherDimensionalLowerBound := by
  intro d hd
  obtain ⟨c, hc, N₀, hN₀, h⟩ := h d hd
  refine ⟨c, hc, N₀, hN₀, ?_⟩
  intro N hN
  obtain ⟨P, hP, hw⟩ := h N hN
  exact ((le_pointDiscrepancy_iff P _).2 hw).trans (pointDiscrepancy_le_worst P hP)

/-- Both versions of the target have exactly the same quantifiers. -/
theorem target_iff_witnessLowerBound : HigherDimensionalLowerBound ↔ WitnessLowerBound := by
  constructor
  · intro h d hd
    obtain ⟨c, hc, N₀, hN₀, h⟩ := h d hd
    exact ⟨c, hc, N₀, hN₀, fun N hN =>
      (le_worstDiscrepancy_iff (by omega) N _).1 (h N hN)⟩
  · exact witnessLowerBound_implies_target

end Tusnady
