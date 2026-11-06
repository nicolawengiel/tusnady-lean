import Tusnady.Boxes.Thresholds
import Tusnady.Boxes.ProductExpansion

/-!
# Comparison with the unchanged orthant discrepancy

The same coloring controls every bounded closed box with a factor `2^d`.
Strict lower cutoffs are realized by closed orthants only on the finite input;
no boundary points are discarded. Conversely each orthant trace on that input
is literally the trace of a valid bounded closed box.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Boxes
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] {d : ℕ}

def corner (P : ι → Point d) (q : Query d) (ε : Fin d → Bool) : Point d :=
  fun j => if ε j then strictThreshold (fun i => P i j) (q.lower j) else q.upper j

theorem interval_indicator (a b t : ℝ) (hab : a ≤ b) :
    (if t ≤ b then (1 : ℝ) else 0) - (if t < a then 1 else 0) =
      if a ≤ t ∧ t ≤ b then 1 else 0 := by
  exact closed_interval_indicator_sub a b t hab

theorem box_indicator_eq_product (P : ι → Point d) (q : Query d) (i : ι) :
    (if P i ∈ q.region then (1 : ℝ) else 0) =
      ∏ j, ((if P i j ≤ q.upper j then 1 else 0) -
        (if P i j ≤ strictThreshold (fun i => P i j) (q.lower j) then 1 else 0)) := by
  classical
  have hcoord : ∀ j,
      ((if P i j ≤ q.upper j then (1 : ℝ) else 0) -
        (if P i j ≤ strictThreshold (fun i => P i j) (q.lower j) then 1 else 0)) =
        (if q.lower j ≤ P i j ∧ P i j ≤ q.upper j then 1 else 0) := by
    intro j
    simpa only [le_strictThreshold_iff (fun i => P i j) (q.lower j) i] using
      interval_indicator _ _ _ (q.valid j)
  simp_rw [hcoord]
  rw [Fintype.prod_boole]
  by_cases h : P i ∈ q.region
  · have h' : ∀ j, q.lower j ≤ P i j ∧ P i j ≤ q.upper j := h
    exact (ite_eq_left h).trans (ite_eq_left h').symm
  · have h' : ¬ ∀ j, q.lower j ≤ P i j ∧ P i j ≤ q.upper j := h
    exact (ite_eq_right h).trans (ite_eq_right h').symm

theorem corner_product_eq_indicator (P : ι → Point d) (q : Query d)
    (ε : Fin d → Bool) (i : ι) :
    (∏ j, if ε j then
      (if P i j ≤ strictThreshold (fun i => P i j) (q.lower j) then (1 : ℝ) else 0)
      else (if P i j ≤ q.upper j then 1 else 0)) =
      if P i ∈ Anchored (corner P q ε) then 1 else 0 := by
  classical
  have hcoord : ∀ j,
      (if ε j then
        (if P i j ≤ strictThreshold (fun i => P i j) (q.lower j) then (1 : ℝ) else 0)
        else (if P i j ≤ q.upper j then 1 else 0)) =
      if P i j ≤ corner P q ε j then 1 else 0 := by
    intro j
    cases hε : ε j <;> simp [corner, hε]
  simp_rw [hcoord]
  rw [Fintype.prod_boole]
  by_cases h : P i ∈ Anchored (corner P q ε)
  · have h' : ∀ j, P i j ≤ corner P q ε j := h
    exact (ite_eq_left h').trans (ite_eq_left h).symm
  · have h' : ¬ ∀ j, P i j ≤ corner P q ε j := h
    exact (ite_eq_right h').trans (ite_eq_right h).symm

theorem realCount_eq_sum_indicator (P : ι → Point d) (χ : ι → ℝ) (q : Query d) :
    realCount P χ q = ∑ i, χ i * (if P i ∈ q.region then (1 : ℝ) else 0) := by
  classical
  simp [realCount, trace, Finset.sum_filter, mul_ite]

theorem realAnchoredCount_eq_sum_indicator (P : ι → Point d) (χ : ι → ℝ) (x : Point d) :
    realAnchoredCount P χ x = ∑ i, χ i * (if P i ∈ Anchored x then (1 : ℝ) else 0) := by
  classical
  simp [realAnchoredCount, Tusnady.trace, Finset.sum_filter, mul_ite]

/-- No new coloring is chosen for individual boxes. This bound applies to an
arbitrary fixed real weighting and every query. -/
theorem abs_realCount_le_of_orthants (P : ι → Point d) (χ : ι → ℝ) (B : ℝ)
    (hbound : ∀ x : Point d, |realAnchoredCount P χ x| ≤ B) (q : Query d) :
    |realCount P χ q| ≤ (2 : ℝ)^d * B := by
  classical
  let f : ι → Fin d → ℝ := fun i j => if P i j ≤ q.upper j then 1 else 0
  let g : ι → Fin d → ℝ := fun i j =>
    if P i j ≤ strictThreshold (fun i => P i j) (q.lower j) then 1 else 0
  have hcorners : ∀ ε : Fin d → Bool,
      |∑ i, χ i * ∏ j, (if ε j then g i j else f i j)| ≤ B := by
    intro ε
    have heq : (∑ i, χ i * ∏ j, (if ε j then g i j else f i j)) =
        realAnchoredCount P χ (corner P q ε) := by
      rw [realAnchoredCount_eq_sum_indicator]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact corner_product_eq_indicator P q ε i
    rw [heq]
    exact hbound _
  have h := abs_weighted_prod_sub_le χ f g B hcorners
  have heq : (∑ i, χ i * ∏ j, (f i j - g i j)) = realCount P χ q := by
    rw [realCount_eq_sum_indicator]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (box_indicator_eq_product P q i).symm
  simpa only [heq, Fintype.card_fin] using h

theorem orthant_coloringDiscrepancy_le (P : ι → Point d) (χ : ι → Bool) :
    Tusnady.coloringDiscrepancy P χ ≤ coloringDiscrepancy P χ := by
  apply (Tusnady.coloringDiscrepancy_le_iff P χ _).mpr
  intro x
  have h := (coloringDiscrepancy_le_iff P χ (coloringDiscrepancy P χ)).mp le_rfl
    (orthantQuery P x)
  simpa only [count, anchoredCount, trace_orthantQuery] using h

theorem coloringDiscrepancy_le_orthant (P : ι → Point d) (χ : ι → Bool) :
    coloringDiscrepancy P χ ≤ (2 : ℝ)^d * Tusnady.coloringDiscrepancy P χ := by
  apply (coloringDiscrepancy_le_iff P χ _).mpr
  intro q
  exact abs_realCount_le_of_orthants P (fun i => sign (χ i))
    (Tusnady.coloringDiscrepancy P χ)
    ((Tusnady.coloringDiscrepancy_le_iff P χ _).mp le_rfl) q

theorem orthant_pointDiscrepancy_le (P : ι → Point d) :
    Tusnady.pointDiscrepancy P ≤ pointDiscrepancy P := by
  classical
  obtain ⟨χ, hχ⟩ := exists_minimizing_coloring P
  rw [hχ]
  exact (Finset.inf'_le _ (Finset.mem_univ χ)).trans (orthant_coloringDiscrepancy_le P χ)

theorem pointDiscrepancy_le_orthant (P : ι → Point d) :
    pointDiscrepancy P ≤ (2 : ℝ)^d * Tusnady.pointDiscrepancy P := by
  classical
  obtain ⟨χ, hχ⟩ := Tusnady.exists_minimizing_coloring P
  rw [hχ]
  exact (Finset.inf'_le _ (Finset.mem_univ χ)).trans (coloringDiscrepancy_le_orthant P χ)

theorem orthant_worstDiscrepancy_le (hd : 0 < d) (N : ℕ) :
    Tusnady.worstDiscrepancy d N ≤ worstDiscrepancy d N := by
  apply csSup_le (Tusnady.configurations_nonempty hd N)
  rintro a ⟨P, hP, rfl⟩
  exact (orthant_pointDiscrepancy_le P).trans (pointDiscrepancy_le_worst P hP)

theorem worstDiscrepancy_le_orthant (hd : 0 < d) (N : ℕ) :
    worstDiscrepancy d N ≤ (2 : ℝ)^d * Tusnady.worstDiscrepancy d N := by
  have hnonempty : {a : ℝ | ∃ P : Fin N → Point d,
      Function.Injective P ∧ pointDiscrepancy P = a}.Nonempty := by
    obtain ⟨_, P, hP, _⟩ := Tusnady.configurations_nonempty hd N
    exact ⟨pointDiscrepancy P, P, hP, rfl⟩
  apply csSup_le hnonempty
  rintro a ⟨P, hP, rfl⟩
  exact (pointDiscrepancy_le_orthant P).trans
    (mul_le_mul_of_nonneg_left (Tusnady.pointDiscrepancy_le_worst P hP) (by positivity))

end Tusnady.Boxes
