import Tusnady.DyadicFunctionsRademacher
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Continuity, real dyadic ancestors, and unit-cube integral interfaces. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.DyadicFunctions
open MeasureTheory Set
open scoped BigOperators

/-- Continuity follows from the actual integral representation. -/
theorem psiBase_continuous : Continuous psiBase := by
  have h := qBase_integrable.continuous_primitive (1:ℝ)
  have heq : psiBase = (fun p => -(∫ x in (1:ℝ)..p, qBase x)) := by
    funext p
    rw [psiBase_eq_primitive, intervalIntegral.integral_symm]
  rw [heq]
  exact h.neg

/-- Affine-localized primitives are globally continuous, including endpoints. -/
theorem psi_continuous (c length : ℝ) : Continuous (psi c length) := by
  unfold psi
  exact continuous_const.mul (psiBase_continuous.comp ((continuous_id.sub continuous_const).div_const length))

/-- The concrete dyadic primitive is continuous. -/
theorem psiI_continuous (a : ℕ) (i : Fin (2^a)) : Continuous (psiI a i) :=
  psi_continuous _ _

lemma dyadicInterval_endpoints (a : ℕ) (i : Fin (2^a)) :
    dyadicInterval a i = Ico ((i.val : ℝ)/(2:ℝ)^a) (((i.val : ℝ)+1)/(2:ℝ)^a) := by
  unfold dyadicInterval dyadicLeft dyadicLength
  congr 1
  ring

/-- Every actual dyadic interval lies in the half-open unit interval. -/
theorem dyadicInterval_subset_unit (a : ℕ) (i : Fin (2^a)) :
    dyadicInterval a i ⊆ Ico (0:ℝ) 1 := by
  rw [dyadicInterval_endpoints]
  intro x hx
  have hp : (0:ℝ) < 2^a := by positivity
  have hi : (i.val : ℝ)+1 ≤ (2:ℝ)^a := by exact_mod_cast i.isLt
  constructor
  · exact (div_nonneg (Nat.cast_nonneg _) hp.le).trans hx.1
  · have hu : ((i.val : ℝ)+1)/(2:ℝ)^a ≤ 1 := (div_le_iff₀ hp).2 (by simpa using hi)
    exact hx.2.trans_le hu

/-- Membership in a finer dyadic interval implies membership in the unique
coarse ancestor obtained in the discrete `ancestorIndex` construction. -/
theorem dyadicInterval_subset_ancestor {a b : ℕ} (ha : a ≤ b) (i : Fin (2^b)) :
    dyadicInterval b i ⊆ dyadicInterval a (Tusnady.Dyadic.ancestorIndex i a ha) := by
  let n : ℕ := i.val / 2^(b-a)
  have hpA : (0:ℝ) < 2^a := by positivity
  have hpB : (0:ℝ) < 2^b := by positivity
  have hpS : (0:ℝ) < 2^(b-a) := by positivity
  have hpow : (2:ℝ)^b = (2:ℝ)^a * (2:ℝ)^(b-a) := by
    rw [← pow_add, Nat.add_sub_of_le ha]
  have hloN : n * 2^(b-a) ≤ i.val := Nat.div_mul_le_self _ _
  have hhiN : i.val+1 ≤ (n+1)*2^(b-a) := by
    have h := Nat.lt_mul_div_succ i.val (by positivity : 0 < 2^(b-a))
    apply Nat.lt_iff_add_one_le.mp
    simpa only [Nat.mul_comm] using h
  have hlo : (n:ℝ)*(2:ℝ)^(b-a) ≤ i.val := by exact_mod_cast hloN
  have hhi : (i.val:ℝ)+1 ≤ ((n:ℝ)+1)*(2:ℝ)^(b-a) := by exact_mod_cast hhiN
  have hleft : (n:ℝ)/(2:ℝ)^a = ((n:ℝ)*(2:ℝ)^(b-a))/(2:ℝ)^b := by
    rw [hpow]
    field_simp
  have hright : ((n:ℝ)+1)/(2:ℝ)^a = (((n:ℝ)+1)*(2:ℝ)^(b-a))/(2:ℝ)^b := by
    rw [hpow]
    field_simp
  rw [dyadicInterval_endpoints, dyadicInterval_endpoints]
  intro x hx
  change (n:ℝ)/(2:ℝ)^a ≤ x ∧ x < ((n:ℝ)+1)/(2:ℝ)^a
  rw [hleft, hright]
  constructor
  · exact (div_le_div_of_nonneg_right hlo hpB.le).trans hx.1
  · exact hx.2.trans_le (div_le_div_of_nonneg_right hhi hpB.le)

/-- Distinct actual dyadic intervals of one depth are disjoint. -/
theorem dyadicInterval_disjoint_same_depth (a : ℕ) (i j : Fin (2^a)) (hij : i ≠ j) :
    Disjoint (dyadicInterval a i) (dyadicInterval a j) := by
  rw [Set.disjoint_left, dyadicInterval_endpoints, dyadicInterval_endpoints]
  intro x hx hy
  have hpos : (0:ℝ) < 2^a := by positivity
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · have hstep : (i.val : ℝ)+1 ≤ j.val := by exact_mod_cast h
    have hbound := div_le_div_of_nonneg_right hstep hpos.le
    exact (not_lt_of_ge (hbound.trans hy.1)) hx.2
  · have hstep : (j.val : ℝ)+1 ≤ i.val := by exact_mod_cast h
    have hbound := div_le_div_of_nonneg_right hstep hpos.le
    exact (not_lt_of_ge (hbound.trans hx.1)) hy.2

/-- Real dyadic intervals, as well as their finite index versions, are
nested or disjoint. -/
theorem dyadicInterval_nested_or_disjoint (a b : ℕ) (i : Fin (2^a)) (j : Fin (2^b)) :
    dyadicInterval a i ⊆ dyadicInterval b j ∨
      dyadicInterval b j ⊆ dyadicInterval a i ∨
        Disjoint (dyadicInterval a i) (dyadicInterval b j) := by
  classical
  rcases le_total a b with hab | hba
  · let k := Tusnady.Dyadic.ancestorIndex j a hab
    by_cases hk : i = k
    · right
      left
      subst i
      exact dyadicInterval_subset_ancestor hab j
    · right
      right
      exact (dyadicInterval_disjoint_same_depth a i k hk).mono_right
        (dyadicInterval_subset_ancestor hab j)
  · let k := Tusnady.Dyadic.ancestorIndex i b hba
    by_cases hk : j = k
    · left
      subst j
      exact dyadicInterval_subset_ancestor hba i
    · right
      right
      exact (dyadicInterval_disjoint_same_depth b k j (Ne.symm hk)).mono_left
        (dyadicInterval_subset_ancestor hba i)

/-- A depth-`a+3` subinterval with index `8i+t` is precisely the `t`th
eighth of the original real interval. -/
lemma dyadicInterval_eq_eighth (a : ℕ) (i : Fin (2^a)) (t : Fin 8)
    (n : Fin (2^(a+3))) (hn : n.val = 8*i.val+t.val) :
    dyadicInterval (a+3) n =
      Ico (dyadicLeft a i + dyadicLength a * cellLo t)
        (dyadicLeft a i + dyadicLength a * cellHi t) := by
  rw [dyadicInterval_endpoints]
  unfold dyadicLeft dyadicLength cellLo cellHi
  rw [hn]
  push_cast
  rw [pow_add]
  norm_num
  congr 1 <;> field_simp
  ring

/-- Every actual finer dyadic interval is an affine region of the primitive
once the depth gap is at least three. Disjoint intervals give the zero affine
function, so no unstated containment assumption is needed. -/
theorem psiI_affine_on_finer (a b : ℕ) (hab : a+3 ≤ b)
    (i : Fin (2^a)) (j : Fin (2^b)) :
    ∃ A B : ℝ, EqOn (psiI a i) (fun x => A*x+B) (dyadicInterval b j) := by
  classical
  let n := Tusnady.Dyadic.ancestorIndex j (a+3) hab
  have hsub : dyadicInterval b j ⊆ dyadicInterval (a+3) n :=
    dyadicInterval_subset_ancestor hab j
  let k := Tusnady.Dyadic.ancestorIndex n a (by omega : a ≤ a+3)
  have hsub' : dyadicInterval (a+3) n ⊆ dyadicInterval a k :=
    dyadicInterval_subset_ancestor (by omega) n
  by_cases hki : k = i
  · have hquot : n.val / 8 = i.val := by
      have hv := congrArg Fin.val hki
      change n.val / 2^((a+3)-a) = i.val at hv
      simpa only [Nat.add_sub_cancel_left, Nat.reducePow] using hv
    let t : Fin 8 := ⟨n.val % 8, Nat.mod_lt _ (by omega)⟩
    have hn : n.val = 8*i.val+t.val := by
      have hmod := Nat.mod_add_div n.val 8
      change n.val = 8*i.val+n.val%8
      rw [hquot] at hmod
      omega
    have heighth := dyadicInterval_eq_eighth a i t n hn
    refine ⟨-walshSign t, walshSign t*dyadicLeft a i + dyadicLength a*primitiveIntercept t, ?_⟩
    intro x hx
    exact psi_affine_on_eighth (dyadicLeft a i) (dyadicLength a) (dyadicLength_pos a) t
      (by rw [← heighth]; exact hsub hx)
  · refine ⟨0, 0, ?_⟩
    intro x hx
    have hnot : x ∉ dyadicInterval a i := by
      intro hxi
      exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a k i hki))
        (hsub' (hsub hx)) hxi
    change psi (dyadicLeft a i) (dyadicLength a) x = 0*x+0
    rw [psi_zero_outside _ _ _ (dyadicLength_pos a) hnot]
    ring

/-- Zero-extension lets an interval integral equal the whole-line integral. -/
lemma integral_unit_eq_global (f : ℝ → ℝ)
    (hf : ∀ x, x ∉ Ico (0:ℝ) 1 → f x = 0) :
    (∫ x in (0:ℝ)..1, f x) = ∫ x, f x := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ico,
    ← integral_indicator measurableSet_Ico]
  congr 1
  funext x
  by_cases hx : x ∈ Ico (0:ℝ) 1 <;> simp [hx, hf x]

lemma qI_zero_outside (a : ℕ) (i : Fin (2^a)) (x : ℝ)
    (hx : x ∉ dyadicInterval a i) : qI a i x = 0 := by
  unfold qI q
  apply qBase_zero_outside
  exact fun h => hx ((normalized_mem_unit_iff _ _ _ (dyadicLength_pos a)).1 h)

lemma psiI_zero_outside (a : ℕ) (i : Fin (2^a)) (x : ℝ)
    (hx : x ∉ dyadicInterval a i) : psiI a i x = 0 :=
  psi_zero_outside _ _ _ (dyadicLength_pos a) hx

/-- The right endpoint lies in `[0,1]`; hence the manuscript's upper bound
one and the localized upper endpoint define the same primitive. -/
theorem psiI_eq_primitive_unit (a : ℕ) (i : Fin (2^a)) (p : ℝ) :
    psiI a i p = ∫ x in p..1, qI a i x := by
  have hend : dyadicLeft a i + dyadicLength a ≤ (1:ℝ) := by
    unfold dyadicLeft dyadicLength
    have hi : (i.val : ℝ)+1 ≤ (2:ℝ)^a := by exact_mod_cast i.isLt
    have hpos : (0:ℝ) < 2^a := by positivity
    have heq : (i.val : ℝ)/(2:ℝ)^a + 1/(2:ℝ)^a = ((i.val : ℝ)+1)/(2:ℝ)^a := by ring
    rw [heq]
    exact (div_le_iff₀ hpos).2 (by simpa using hi)
  have hzero : (∫ x in dyadicLeft a i + dyadicLength a..1, qI a i x) = 0 := by
    calc
      _ = ∫ _x in dyadicLeft a i + dyadicLength a..1, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hend] at hx
        exact qI_zero_outside a i x (fun h => (not_lt_of_ge hx.1) h.2)
      _ = 0 := by simp
  have hcomp : Integrable (qI a i) := by
    exact (qBase_integrable.comp_div (ne_of_gt (dyadicLength_pos a))).comp_sub_right (dyadicLeft a i)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcomp.intervalIntegrable (a := p) (b := dyadicLeft a i + dyadicLength a))
    (hcomp.intervalIntegrable (a := dyadicLeft a i + dyadicLength a) (b := 1))
  rw [hzero, add_zero] at hsplit
  rw [← hsplit]
  exact psi_eq_primitive _ _ _ (dyadicLength_pos a)

/-- Manuscript moments are stated over `[0,1]`, not merely over `ℝ`. -/
theorem integral_unit_qI_moment (a : ℕ) (i : Fin (2^a)) (n : ℕ) (hn : n ≤ 2) :
    (∫ x in (0:ℝ)..1, qI a i x*x^n) = 0 := by
  rw [integral_unit_eq_global]
  · exact integral_qI_moment a i n hn
  · intro x hx
    rw [qI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h)), zero_mul]

/-- Zeroth primitive moment in the original unit domain. -/
theorem integral_unit_psiI (a : ℕ) (i : Fin (2^a)) :
    (∫ x in (0:ℝ)..1, psiI a i x) = 0 := by
  rw [integral_unit_eq_global]
  · exact integral_psi _ _ (dyadicLength_pos a)
  · intro x hx
    exact psiI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h))

/-- First primitive moment in the original unit domain. -/
theorem integral_unit_psiI_mul_id (a : ℕ) (i : Fin (2^a)) :
    (∫ x in (0:ℝ)..1, x*psiI a i x) = 0 := by
  rw [integral_unit_eq_global]
  · simpa only [psiI, mul_comm] using
      integral_psi_mul_id (dyadicLeft a i) (dyadicLength a) (dyadicLength_pos a)
  · intro x hx
    rw [psiI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h)), mul_zero]

/-- The exact `|I|³/192` norm in the manuscript's integration domain. -/
theorem integral_unit_psiI_sq (a : ℕ) (i : Fin (2^a)) :
    (∫ x in (0:ℝ)..1, psiI a i x^2) = dyadicLength a^3/192 := by
  rw [integral_unit_eq_global]
  · exact integral_psiI_sq a i
  · intro x hx
    rw [psiI_zero_outside a i x (fun h => hx (dyadicInterval_subset_unit a i h)), zero_pow (by omega)]

/-- Exact dyadic L¹ mass. -/
theorem integral_abs_qI (a : ℕ) (i : Fin (2^a)) :
    (∫ x, |qI a i x|) = dyadicLength a := by
  have hfun : (fun x => |qI a i x|) =
      (dyadicInterval a i).indicator (fun _ => (1:ℝ)) := by
    funext x
    exact abs_q _ _ _ (dyadicLength_pos a)
  rw [hfun]
  unfold dyadicInterval
  rw [integral_indicator measurableSet_Ico, integral_const]
  simp only [Measure.restrict_apply_univ, smul_eq_mul, mul_one, measureReal_def,
    Real.volume_Ico, ENNReal.toReal_ofReal']
  rw [add_sub_cancel_left, max_eq_left (dyadicLength_pos a).le]

/-- Exact dyadic L² mass of the Walsh function. -/
theorem integral_qI_sq (a : ℕ) (i : Fin (2^a)) :
    (∫ x, qI a i x^2) = dyadicLength a := by
  have hfun : (fun x => qI a i x^2) = (fun x => |qI a i x|) := by
    funext x
    have habs := abs_q (dyadicLeft a i) (dyadicLength a) x (dyadicLength_pos a)
    change |qI a i x| = (dyadicInterval a i).indicator (fun _ => (1:ℝ)) x at habs
    by_cases hx : x ∈ dyadicInterval a i
    · rw [Set.indicator_of_mem hx] at habs
      rw [← sq_abs, habs]
      norm_num
    · rw [qI_zero_outside a i x hx]
      norm_num
  rw [hfun]
  exact integral_abs_qI a i

/-- The primitive is orthogonal to every function that agrees with an
affine function on its support. No condition outside the support is needed. -/
theorem psiI_orthogonal_affine_on (a : ℕ) (i : Fin (2^a)) (g : ℝ → ℝ) (A B : ℝ)
    (hg : EqOn g (fun x => A*x+B) (dyadicInterval a i)) :
    (∫ x in (0:ℝ)..1, psiI a i x * g x) = 0 := by
  have hfun : (fun x => psiI a i x*g x) =
      (fun x => A*(x*psiI a i x) + B*psiI a i x) := by
    funext x
    by_cases hx : x ∈ dyadicInterval a i
    · rw [hg hx]
      ring
    · rw [psiI_zero_outside a i x hx]
      ring
  have h₁ : IntervalIntegrable (fun x => A*(x*psiI a i x)) volume 0 1 :=
    (continuous_const.mul (continuous_id.mul (psiI_continuous a i))).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun x => B*psiI a i x) volume 0 1 :=
    (continuous_const.mul (psiI_continuous a i)).intervalIntegrable _ _
  rw [hfun, intervalIntegral.integral_add h₁ h₂, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_unit_psiI_mul_id, integral_unit_psiI]
  ring

/-- Walsh functions are constant on every dyadic interval whose depth
is at least three levels finer, including intervals outside the support. -/
theorem qI_constant_on_finer (a b : ℕ) (hab : a+3 ≤ b)
    (i : Fin (2^a)) (j : Fin (2^b)) :
    ∃ value : ℝ, EqOn (qI a i) (fun _ => value) (dyadicInterval b j) := by
  classical
  let n := Tusnady.Dyadic.ancestorIndex j (a+3) hab
  have hsub : dyadicInterval b j ⊆ dyadicInterval (a+3) n :=
    dyadicInterval_subset_ancestor hab j
  let k := Tusnady.Dyadic.ancestorIndex n a (by omega : a ≤ a+3)
  have hsub' : dyadicInterval (a+3) n ⊆ dyadicInterval a k :=
    dyadicInterval_subset_ancestor (by omega) n
  by_cases hki : k = i
  · have hquot : n.val / 8 = i.val := by
      have hv := congrArg Fin.val hki
      change n.val / 2^((a+3)-a) = i.val at hv
      simpa only [Nat.add_sub_cancel_left, Nat.reducePow] using hv
    let t : Fin 8 := ⟨n.val % 8, Nat.mod_lt _ (by omega)⟩
    have hn : n.val = 8*i.val+t.val := by
      have hmod := Nat.mod_add_div n.val 8
      change n.val = 8*i.val+n.val%8
      rw [hquot] at hmod
      omega
    have heighth := dyadicInterval_eq_eighth a i t n hn
    refine ⟨walshSign t, ?_⟩
    intro x hx
    have hxe : x ∈ Ico (dyadicLeft a i+dyadicLength a*cellLo t)
        (dyadicLeft a i+dyadicLength a*cellHi t) := by
      rw [← heighth]
      exact hsub hx
    apply qBase_on_cell t ((x-dyadicLeft a i)/dyadicLength a)
    constructor
    · apply (le_div_iff₀ (dyadicLength_pos a)).2
      linarith [hxe.1]
    · apply (div_lt_iff₀ (dyadicLength_pos a)).2
      linarith [hxe.2]
  · refine ⟨0, ?_⟩
    intro x hx
    have hnot : x ∉ dyadicInterval a i := by
      intro hxi
      exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a k i hki))
        (hsub' (hsub hx)) hxi
    exact qI_zero_outside a i x hnot

/-- Orthogonality of primitives at depths separated by three, proved using
actual reals, affine localization, and the two primitive moments. -/
theorem integral_psiI_mul_psiI_separated (a b : ℕ) (hab : a+3 ≤ b)
    (i : Fin (2^a)) (j : Fin (2^b)) :
    (∫ x in (0:ℝ)..1, psiI a i x*psiI b j x) = 0 := by
  obtain ⟨A, B, h⟩ := psiI_affine_on_finer a b hab i j
  simpa only [mul_comm] using psiI_orthogonal_affine_on b j (psiI a i) A B h

/-- Orthogonality for distinct real dyadic intervals of equal depth. -/
theorem integral_psiI_mul_psiI_same_depth (a : ℕ)
    (i j : Fin (2^a)) (hij : i ≠ j) :
    (∫ x in (0:ℝ)..1, psiI a i x*psiI a j x) = 0 := by
  have hfun : (fun x => psiI a i x*psiI a j x) = (fun _ => (0:ℝ)) := by
    funext x
    by_cases hx : x ∈ dyadicInterval a i
    · have hxj : x ∉ dyadicInterval a j := by
        intro h
        exact (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a i j hij)) hx h
      rw [psiI_zero_outside a j x hxj, mul_zero]
    · rw [psiI_zero_outside a i x hx, zero_mul]
  rw [hfun]
  simp

end Tusnady.DyadicFunctions
