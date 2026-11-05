import Tusnady.CellComponents

/-!
# Retained-component deficit geometry and finite counting

The retained set is the actual computed high-projection component set. Its
indices inject into nonnegative deficits, whose total is at most e+2d.
When the first coordinate is modulated, it contributes no choice, leaving
exactly d-1 free deficit coordinates. This proves the required polynomial
retained-cardinality bound without a counting hypothesis.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.DyadicFunctions Tusnady.Haar
open scoped BigOperators

def componentDeficit (j : ℕ) (modulated : Bool) : ComponentIndex j modulated → ℕ := by
  cases modulated with
  | true => exact fun _ => 0
  | false => exact fun b => match b with | none => j+1 | some b => j-b.val

theorem componentDeficit_injective (j : ℕ) (m : Bool) :
    Function.Injective (componentDeficit j m) := by
  cases m with
  | true =>
    change Function.Injective (fun _ : Unit => (0:ℕ))
    exact fun _ _ _ => Subsingleton.elim _ _
  | false =>
    intro b c h
    cases b with
    | none =>
      cases c with
      | none => rfl
      | some c => simp only [componentDeficit] at h; omega
    | some b =>
      cases c with
      | none => simp only [componentDeficit] at h; omega
      | some c =>
        congr 1
        apply Fin.ext
        simp only [componentDeficit] at h
        have hb := b.isLt
        have hc := c.isLt
        omega

def modulationCorrection (m : Bool) : ℤ := if m then 2 else 0

/-- Component levels equal depth minus the explicit nonnegative deficit,
plus two precisely in the modulated coordinates. -/
theorem componentFactor_level (H j : ℕ) (hj : j+2 < H) (i : Fin (2^j))
    (m : Bool) (b : ComponentIndex j m) :
    factorLevel (componentFactor H j hj i m b) =
      (j:ℤ)-(componentDeficit j m b:ℤ)+modulationCorrection m := by
  cases m with
  | true => simp [componentFactor, factorLevel, componentDeficit, modulationCorrection]
  | false =>
    cases b with
    | none => simp [componentFactor, factorLevel, componentDeficit, modulationCorrection]
    | some b =>
      simp only [componentFactor, factorLevel, componentDeficit, modulationCorrection, Bool.false_eq_true,
        if_false, add_zero]
      rw [Nat.cast_sub b.isLt.le]
      ring

def componentDeficitSum {d : ℕ} (j : Fin d → ℕ) (m : Fin d → Bool) (b : ComponentChoices j m) : ℕ :=
  ∑ k, componentDeficit (j k) (m k) (b k)

def correctionSum {d : ℕ} (m : Fin d → Bool) : ℤ := ∑ k, modulationCorrection (m k)

lemma correctionSum_le {d : ℕ} (m : Fin d → Bool) : correctionSum m ≤ 2*(d:ℤ) := by
  have h : ∀ k : Fin d, modulationCorrection (m k) ≤ 2 := by
    intro k
    cases h : m k <;> norm_num [modulationCorrection, h]
  calc
    correctionSum m ≤ ∑ _k : Fin d, (2:ℤ) := Finset.sum_le_sum (fun k _ => h k)
    _ = 2*(d:ℤ) := by simp; ring

lemma componentFactor_total_level {d H : ℕ} (j : Fin d → ℕ) (hj : ∀ k, j k+2 < H)
    (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool) (b : ComponentChoices j m) :
    tensorFactorLevel (cellComponentFactors j hj I m b) =
      ((∑ k, j k : ℕ):ℤ)-(componentDeficitSum j m b:ℤ)+correctionSum m := by
  unfold tensorFactorLevel cellComponentFactors
  simp_rw [componentFactor_level]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, componentDeficitSum,
    correctionSum, Nat.cast_sum]

/-- Retention itself bounds the total geometric deficit by e+2d. -/
theorem retained_deficit_sum_le {d H : ℕ} (h e : ℕ) (j : Fin d → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool)
    (hjoin : ∑ k, j k = h+e) (b : ComponentChoices j m)
    (hb : b ∈ retainedComponents h j hj I m) :
    componentDeficitSum j m b ≤ e+2*d := by
  have hr : (h:ℤ) ≤ tensorFactorLevel (cellComponentFactors j hj I m b) := by
    simpa only [retainedComponents, Finset.mem_filter, Finset.mem_univ, true_and] using hb
  rw [componentFactor_total_level, hjoin] at hr
  have hc := correctionSum_le m
  push_cast at hr
  omega

lemma componentDeficit_le_sum {d : ℕ} (j : Fin d → ℕ) (m : Fin d → Bool)
    (b : ComponentChoices j m) (k : Fin d) :
    componentDeficit (j k) (m k) (b k) ≤ componentDeficitSum j m b := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (componentDeficit (j i) (m i) (b i)))
    (Finset.mem_univ k)

/-- Encode only the non-first deficits. The first coordinate is modulated
and hence has the unique component. -/
def retainedDeficitCode {n H : ℕ} (h e : ℕ) (j : Fin (n+1) → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin (n+1) → Bool)
    (hjoin : ∑ k, j k = h+e)
    (b : {b // b ∈ retainedComponents h j hj I m}) : Fin n → Fin (e+2*(n+1)+1) :=
  fun k => ⟨componentDeficit (j k.succ) (m k.succ) (b.val k.succ),
    Nat.lt_succ_of_le ((componentDeficit_le_sum j m b.val k.succ).trans
      (retained_deficit_sum_le h e j hj I m hjoin b.val b.property))⟩

theorem retainedDeficitCode_injective {n H : ℕ} (h e : ℕ) (j : Fin (n+1) → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin (n+1) → Bool)
    (hjoin : ∑ k, j k = h+e) (hm0 : m 0 = true) :
    Function.Injective (retainedDeficitCode h e j hj I m hjoin) := by
  intro b c hbc
  apply Subtype.ext
  funext k
  refine Fin.cases ?_ (fun r => ?_) k
  · have hsub : Subsingleton (ComponentIndex (j 0) (m 0)) := by
      rw [hm0]
      dsimp [ComponentIndex]
      infer_instance
    exact @Subsingleton.elim _ hsub (b.val 0) (c.val 0)
  · apply componentDeficit_injective (j r.succ) (m r.succ)
    exact congrArg (fun code => (code r).val) hbc

/-- Exact d-1-dimensional deficit-cube bound for the retained cardinality. -/
theorem retained_card_le_deficit_cube {n H : ℕ} (h e : ℕ) (j : Fin (n+1) → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin (n+1) → Bool)
    (hjoin : ∑ k, j k = h+e) (hm0 : m 0 = true) :
    (retainedComponents h j hj I m).card ≤ (e+2*(n+1)+1)^n := by
  have hc := Fintype.card_le_of_injective (retainedDeficitCode h e j hj I m hjoin)
    (retainedDeficitCode_injective h e j hj I m hjoin hm0)
  simpa only [Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using hc

/-- Polynomial bound of the exact manuscript degree d-1. The explicit
constant is (2d+1)^(d-1), with d=n+1. -/
theorem retained_card_le_polynomial {n H : ℕ} (h e : ℕ) (j : Fin (n+1) → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin (n+1) → Bool)
    (hjoin : ∑ k, j k = h+e) (hm0 : m 0 = true) :
    (retainedComponents h j hj I m).card ≤ (2*(n+1)+1)^n*(e+1)^n := by
  have hbase : e+2*(n+1)+1 ≤ (2*(n+1)+1)*(e+1) := by nlinarith
  calc
    _ ≤ (e+2*(n+1)+1)^n := retained_card_le_deficit_cube h e j hj I m hjoin hm0
    _ ≤ ((2*(n+1)+1)*(e+1))^n := Nat.pow_le_pow_left hbase n
    _ = _ := by rw [Nat.mul_pow]

end Tusnady.Cell
