import Tusnady.DyadicFunctions

/-! # Identification of the explicit base primitive with its actual integral. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace Tusnady.DyadicFunctions
open MeasureTheory Set
open scoped BigOperators

lemma cellHi_le_one (i : Fin 8) : cellHi i ≤ 1 := by
  have hi : i.val + 1 ≤ 8 := i.isLt
  have hi' : (i.val : ℝ) + 1 ≤ 8 := by exact_mod_cast hi
  unfold cellHi
  linarith

lemma cellLo_nonneg (i : Fin 8) : 0 ≤ cellLo i := by
  unfold cellLo
  positivity

lemma baseCell_subset_unit (i : Fin 8) : baseCell i ⊆ Ico (0:ℝ) 1 := by
  intro p hp
  exact ⟨le_trans (cellLo_nonneg i) hp.1, lt_of_lt_of_le hp.2 (cellHi_le_one i)⟩

/-- The real eighth-cells cover the half-open unit interval. -/
lemma exists_baseCell (p : ℝ) (hp : p ∈ Ico (0:ℝ) 1) :
    ∃ i : Fin 8, p ∈ baseCell i := by
  have hnonneg : 0 ≤ 8 * p := by linarith [hp.1]
  have hlt : ⌊8*p⌋₊ < 8 := (Nat.floor_lt hnonneg).2 (by norm_num; linarith [hp.2])
  refine ⟨⟨⌊8*p⌋₊, hlt⟩, ?_⟩
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one (8*p)
  change (⌊8*p⌋₊ : ℝ)/8 ≤ p ∧ p < ((⌊8*p⌋₊ : ℝ)+1)/8
  constructor <;> linarith

lemma qBase_on_cell (i : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    qBase p = walshSign i := patch_sum_eval (fun j _ => walshSign j) i p hp

lemma psiBase_on_cell (i : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    psiBase p = -walshSign i * p + primitiveIntercept i :=
  patch_sum_eval primitivePiece i p hp

lemma qBase_zero_outside (p : ℝ) (hp : p ∉ Ico (0:ℝ) 1) : qBase p = 0 := by
  exact patch_sum_zero (fun i _ => walshSign i) p
    (fun i hi => hp (baseCell_subset_unit i hi))

lemma psiBase_zero_outside (p : ℝ) (hp : p ∉ Ico (0:ℝ) 1) : psiBase p = 0 := by
  exact patch_sum_zero primitivePiece p (fun i hi => hp (baseCell_subset_unit i hi))

/-- Pointwise absolute value, including all half-open boundary conventions. -/
theorem abs_qBase (p : ℝ) : |qBase p| = (Ico (0:ℝ) 1).indicator (fun _ => (1:ℝ)) p := by
  by_cases hp : p ∈ Ico (0:ℝ) 1
  · obtain ⟨i, hi⟩ := exists_baseCell p hp
    rw [qBase_on_cell i p hi]
    simp only [Set.indicator_of_mem hp]
    fin_cases i <;> norm_num [walshSign]
  · rw [qBase_zero_outside p hp]
    simp [hp]

lemma qBase_integrable : Integrable qBase := by
  exact integrable_finset_sum Finset.univ (fun i _ => patch_integrable i _ continuous_const)

lemma psiBase_integrable : Integrable psiBase := by
  exact integrable_finset_sum Finset.univ
    (fun i _ => patch_integrable i _ (by unfold primitivePiece; fun_prop))

/-- Integral of one Walsh patch, expressed by the actual overlap length. -/
lemma integral_patch_right (i : Fin 8) (p s : ℝ) (hp : p ≤ 1) :
    (∫ x in p..1, patch i (fun _ => s) x) =
      max (cellHi i - max (cellLo i) p) 0 * s := by
  rw [intervalIntegral.integral_of_le hp, ← integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ico]
  unfold patch baseCell
  rw [integral_indicator measurableSet_Ico, Measure.restrict_restrict measurableSet_Ico,
    Ico_inter_Ico]
  change (∫ _x in Ico (max (cellLo i) p) (min (cellHi i) 1), s) = _
  rw [min_eq_left (cellHi_le_one i)]
  rw [integral_const]
  simp only [Measure.restrict_apply_univ, smul_eq_mul, measureReal_def, Real.volume_Ico,
    ENNReal.toReal_ofReal']

/-- Actual right primitive as a finite sum of clipped affine functions. -/
theorem qBase_primitive_formula (p : ℝ) (hp : p ≤ 1) :
    (∫ x in p..1, qBase x) =
      ∑ i : Fin 8, max (cellHi i - max (cellLo i) p) 0 * walshSign i := by
  change (∫ x in p..1, ∑ i : Fin 8, patch i (fun _ => walshSign i) x) = _
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_patch_right i p (walshSign i) hp
  · intro i _
    exact (patch_integrable i _ continuous_const).intervalIntegrable

/-- The overlap of a right ray with an eighth-cell, using the order
of the actual disjoint dyadic pieces. -/
lemma overlap_length (i j : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    max (cellHi j - max (cellLo j) p) 0 =
      if j.val < i.val then 0 else if j.val = i.val then cellHi i - p else 1/8 := by
  change cellLo i ≤ p ∧ p < cellHi i at hp
  by_cases hji : j.val < i.val
  · rw [if_pos hji]
    have hstep : j.val + 1 ≤ i.val := hji
    have hstep' : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hstep
    have hhi : cellHi j ≤ p := by unfold cellHi cellLo at *; linarith
    have hlo : cellLo j ≤ p := le_trans (cellLo_le_cellHi j) hhi
    rw [max_eq_right hlo, max_eq_right (sub_nonpos.mpr hhi)]
  · rw [if_neg hji]
    by_cases heq : j.val = i.val
    · have heqFin : j = i := Fin.ext heq
      subst j
      rw [if_pos rfl, max_eq_right hp.1, max_eq_left (sub_nonneg.mpr hp.2.le)]
    · rw [if_neg heq]
      have hstep : i.val + 1 ≤ j.val := by omega
      have hstep' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hstep
      have hlo : p ≤ cellLo j := by unfold cellHi cellLo at *; linarith
      have hlength : cellHi j - cellLo j = (1:ℝ)/8 := by unfold cellHi cellLo; ring
      rw [max_eq_left hlo, hlength, max_eq_left (by norm_num : (0:ℝ) ≤ 1/8)]

/-- On its own cell the explicit primitive is the integral of `qBase`. -/
theorem psiBase_eq_primitive_on_cell (i : Fin 8) (p : ℝ) (hp : p ∈ baseCell i) :
    psiBase p = ∫ x in p..1, qBase x := by
  have hpone : p ≤ 1 := le_trans hp.2.le (cellHi_le_one i)
  rw [qBase_primitive_formula p hpone]
  change (∑ j : Fin 8, patch j (primitivePiece j) p) = _
  rw [patch_sum_eval primitivePiece i p hp]
  simp_rw [overlap_length i _ p hp]
  fin_cases i <;>
    norm_num [Fin.sum_univ_succ, primitivePiece, primitiveIntercept, walshSign,
      cellLo, cellHi] <;> ring

/-- The explicit affine-patch function is the actual right primitive
at every real argument, with zero extension outside the unit interval. -/
theorem psiBase_eq_primitive (p : ℝ) : psiBase p = ∫ x in p..1, qBase x := by
  by_cases hp0 : p < 0
  · have hout : p ∉ Ico (0:ℝ) 1 := fun h => (not_le_of_gt hp0) h.1
    rw [psiBase_zero_outside p hout, qBase_primitive_formula p (by linarith)]
    have hmax : ∀ i : Fin 8, max (cellLo i) p = cellLo i :=
      fun i => max_eq_left (by linarith [cellLo_nonneg i])
    simp_rw [hmax]
    have hlength : ∀ i : Fin 8, cellHi i - cellLo i = (1:ℝ)/8 := by
      intro i
      unfold cellHi cellLo
      ring
    simp_rw [hlength, max_eq_left (by norm_num : (0:ℝ) ≤ 1/8)]
    norm_num [Fin.sum_univ_succ, walshSign]
  · by_cases hp1 : p < 1
    · obtain ⟨i, hi⟩ := exists_baseCell p ⟨le_of_not_gt hp0, hp1⟩
      exact psiBase_eq_primitive_on_cell i p hi
    · have hpge : 1 ≤ p := le_of_not_gt hp1
      have hout : p ∉ Ico (0:ℝ) 1 := fun h => hp1 h.2
      rw [psiBase_zero_outside p hout]
      symm
      calc
        (∫ x in p..1, qBase x) = ∫ _x in p..1, (0:ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_ge hpge] at hx
          exact qBase_zero_outside x (fun h => (not_lt_of_ge hx.1) h.2)
        _ = 0 := by simp

/-- The primitive is affine on each of the eight real dyadic pieces. -/
theorem psiBase_affine_on_cell (i : Fin 8) :
    EqOn psiBase (fun p => -walshSign i * p + primitiveIntercept i) (baseCell i) :=
  fun p hp => psiBase_on_cell i p hp

end Tusnady.DyadicFunctions
