import Tusnady.Definitions
import Wei.R56Audit.SupNorm

/-!
# Coordinates and colorings for Zhewei Wei's planar lower bound

Wei's imported software remains MIT copyright (c) 2026 Zhewei Wei; its fixed
source and adaptation are recorded in `vendor/wei-6f14d177`.
These project bridge lemmas identify its product coordinates, integer-unit
colorings and closed anchored rectangle sums with our existing definitions.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.PlanarWei

/-- The two actual coordinates; no geometric or cardinality hypothesis. -/
def pointEquiv : (ℝ × ℝ) ≃ Point 2 where
  toFun := fun p => ![p.1, p.2]
  invFun := fun p => (p 0, p 1)
  left_inv := by intro p; rfl
  right_inv := by intro p; ext i; fin_cases i <;> rfl

@[simp] lemma pointEquiv_zero (p : ℝ × ℝ) : pointEquiv p 0 = p.1 := rfl
@[simp] lemma pointEquiv_one (p : ℝ × ℝ) : pointEquiv p 1 = p.2 := rfl

/-- Distinctness survives the coordinate representation change. -/
lemma injective_points {N : ℕ} {P : Fin N → ℝ × ℝ} (hP : Function.Injective P) :
    Function.Injective (fun i => pointEquiv (P i)) := pointEquiv.injective.comp hP

lemma mem_anchored_pointEquiv (p : ℝ × ℝ) (x y : ℝ) :
    pointEquiv p ∈ Anchored (pointEquiv (x,y)) ↔ p.1 ≤ x ∧ p.2 ≤ y := by
  constructor
  · intro h
    exact ⟨h 0, h 1⟩
  · rintro ⟨hx, hy⟩ i
    fin_cases i
    · exact hx
    · exact hy

/-- An actual unit coloring is a real sign coloring. -/
lemma units_isSignColoring {N : ℕ} (χ : Fin N → ℤˣ) :
    IsSignColoring (fun i => (((χ i : ℤˣ) : ℤ) : ℝ)) := by
  intro i
  rcases Int.units_eq_one_or (χ i) with h | h
  · right
    simp only [h, Units.val_one, Int.cast_one]
  · left
    simp only [h, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]

/-- A unit representative for every real ±1 coloring, including choices that
depend on the point configuration. -/
def unitsOfColoring {N : ℕ} (χ : Fin N → ℝ) : Fin N → ℤˣ :=
  fun i => if χ i = 1 then 1 else -1

lemma unitsOfColoring_coe {N : ℕ} (χ : Fin N → ℝ) (hχ : IsSignColoring χ) (i : Fin N) :
    (((unitsOfColoring χ i : ℤˣ) : ℤ) : ℝ) = χ i := by
  rcases hχ i with h | h <;> norm_num [unitsOfColoring, h]

/-- On points in the nonnegative quadrant, a closed lower orthant and Wei's
closed rectangle anchored at zero have exactly the same incidence pattern. -/
lemma anchored_iff_rectangle (p : ℝ × ℝ) (hp : 0 ≤ p) (x y : ℝ) :
    pointEquiv p ∈ Anchored (pointEquiv (x,y)) ↔ p ∈ Set.Icc 0 (x,y) := by
  rw [mem_anchored_pointEquiv]
  constructor
  · exact fun h => ⟨hp, h⟩
  · exact fun h => h.2

/-- Exact equality of the two signed finite sums. -/
lemma realAnchoredCount_eq_F {N : ℕ} (P : Fin N → ℝ × ℝ)
    (hP : ∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) (χ : Fin N → ℤˣ) (x y : ℝ) :
    realAnchoredCount (fun i => pointEquiv (P i))
      (fun i => (((χ i : ℤˣ) : ℤ) : ℝ)) (pointEquiv (x,y)) = R56Audit.F χ P x y := by
  classical
  unfold realAnchoredCount trace R56Audit.F
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  rw [anchored_iff_rectangle (P i) (hP i).1 x y]
  by_cases hmem : P i ∈ Set.Icc (0 : ℝ × ℝ) (x,y)
  · simp [hmem]
  · simp [hmem]

lemma realAnchoredCount_eq_F_unitsOfColoring {N : ℕ} (P : Fin N → ℝ × ℝ)
    (hP : ∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1)
    (χ : Fin N → ℝ) (hχ : IsSignColoring χ) (x y : ℝ) :
    realAnchoredCount (fun i => pointEquiv (P i)) χ (pointEquiv (x,y)) =
      R56Audit.F (unitsOfColoring χ) P x y := by
  have h := realAnchoredCount_eq_F P hP (unitsOfColoring χ) x y
  simpa only [unitsOfColoring_coe χ hχ] using h

/-- Supremum attainment produces an actual orthant for every real coloring. -/
theorem pointDiscrepancy_ge_of_units_supNorm {N : ℕ} (P : Fin N → ℝ × ℝ)
    (hP : ∀ i, P i ∈ Set.Icc (0 : ℝ × ℝ) 1) (t : ℝ)
    (h : ∀ χ : Fin N → ℤˣ, t < R56Audit.supNorm χ P) :
    t ≤ pointDiscrepancy (fun i => pointEquiv (P i)) := by
  apply (le_pointDiscrepancy_iff_real_colorings _ _).mpr
  intro χ hχ
  obtain ⟨x, hx, y, hy, hmax⟩ := R56Audit.exists_eq_supNorm (unitsOfColoring χ) P
  refine ⟨pointEquiv (x,y), ?_⟩
  rw [realAnchoredCount_eq_F_unitsOfColoring P hP χ hχ x y, hmax]
  exact (h (unitsOfColoring χ)).le

end Tusnady.PlanarWei
