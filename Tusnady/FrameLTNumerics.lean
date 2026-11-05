import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! The numerical iteration in the unweighted frame-discretization proof.
The exponential potential below controls the ratio without an unproved
infinite-product estimate. No frame-selection existence is asserted here. -/

noncomputable section
namespace Tusnady.Frame

def lowerStep (δ α : ℝ) : ℝ := α * (1 - 5 * Real.sqrt (δ / α)) / 2
def upperStep (δ α β : ℝ) : ℝ := β * (1 + 5 * Real.sqrt (δ / α)) / 2

lemma step_sqrt_le {δ α : ℝ} (hδ : 0 < δ) (hα : 100 * δ ≤ α) :
    Real.sqrt (δ / α) ≤ 1 / 10 := by
  have ha : 0 < α := lt_of_lt_of_le (by positivity) hα
  have hd : 0 ≤ δ / α := div_nonneg hδ.le ha.le
  have hds : (Real.sqrt (δ / α)) ^ 2 = δ / α := Real.sq_sqrt hd
  have hdiv : δ / α ≤ 1 / 100 := (div_le_iff₀ ha).mpr (by linarith)
  nlinarith [Real.sqrt_nonneg (δ / α)]

lemma lowerStep_bounds {δ α : ℝ} (hδ : 0 < δ) (hα : 100 * δ ≤ α) :
    α / 4 ≤ lowerStep δ α ∧ lowerStep δ α ≤ α / 2 := by
  have ha : 0 ≤ α := le_trans (by positivity) hα
  have ht := step_sqrt_le hδ hα
  have hn := Real.sqrt_nonneg (δ / α)
  unfold lowerStep
  constructor <;> nlinarith

lemma lowerStep_pos {δ α : ℝ} (hδ : 0 < δ) (hα : 100 * δ ≤ α) :
    0 < lowerStep δ α :=
  lt_of_lt_of_le (by linarith) (lowerStep_bounds hδ hα).1

lemma step_sqrt_growth {δ α : ℝ} (hδ : 0 < δ) (hα : 100 * δ ≤ α) :
    (4 / 3 : ℝ) * Real.sqrt (δ / α) ≤ Real.sqrt (δ / lowerStep δ α) := by
  have ha : 0 < α := lt_of_lt_of_le (by positivity) hα
  have hb := lowerStep_pos hδ hα
  have hs := (lowerStep_bounds hδ hα).2
  have hd : 0 ≤ δ / α := div_nonneg hδ.le ha.le
  have he : 0 ≤ δ / lowerStep δ α := div_nonneg hδ.le hb.le
  have hdiv : δ / (α / 2) ≤ δ / lowerStep δ α :=
    div_le_div_of_nonneg_left hδ.le hb hs
  have heq : δ / (α / 2) = 2 * (δ / α) := by field_simp
  rw [heq] at hdiv
  have ht := Real.sq_sqrt hd
  have hu := Real.sq_sqrt he
  nlinarith [Real.sqrt_nonneg (δ / α), Real.sqrt_nonneg (δ / lowerStep δ α)]

lemma step_exponential_factor {δ α : ℝ} (hδ : 0 < δ) (hα : 100 * δ ≤ α) :
    (1 + 5 * Real.sqrt (δ / α)) * Real.exp (60 * Real.sqrt (δ / α)) ≤
      (1 - 5 * Real.sqrt (δ / α)) *
        Real.exp (60 * Real.sqrt (δ / lowerStep δ α)) := by
  let t := Real.sqrt (δ / α)
  let t' := Real.sqrt (δ / lowerStep δ α)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht1 : t ≤ 1 / 10 := step_sqrt_le hδ hα
  have hfactor : 0 ≤ 1 - 5 * t := by linarith
  have hsmall : 1 + 5 * t ≤ (1 - 5 * t) * Real.exp (20 * t) := by
    have he := Real.add_one_le_exp (20 * t)
    have hh := mul_le_mul_of_nonneg_left he hfactor
    nlinarith [mul_nonneg ht (show 1 - 10 * t ≥ 0 by linarith)]
  have hgrowth : 80 * t ≤ 60 * t' := by
    have h := step_sqrt_growth hδ hα
    change (4 / 3 : ℝ) * t ≤ t' at h
    linarith
  calc
    (1 + 5 * t) * Real.exp (60 * t) ≤
        ((1 - 5 * t) * Real.exp (20 * t)) * Real.exp (60 * t) :=
      mul_le_mul_of_nonneg_right hsmall (Real.exp_pos _).le
    _ = (1 - 5 * t) * Real.exp (80 * t) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (1 - 5 * t) * Real.exp (60 * t') :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hgrowth) hfactor

/-- The LT ratio-control step, proved using an explicit exponential
potential. The numerical constant is universal. -/
lemma step_potential {δ α β C : ℝ} (hδ : 0 < δ) (hα : 100 * δ ≤ α)
    (hC : 0 ≤ C)
    (hβ : β ≤ C * α * Real.exp (60 * Real.sqrt (δ / α))) :
    upperStep δ α β ≤ C * lowerStep δ α *
      Real.exp (60 * Real.sqrt (δ / lowerStep δ α)) := by
  have ha : 0 ≤ α := le_trans (by positivity) hα
  have ht : 0 ≤ 1 + 5 * Real.sqrt (δ / α) := by positivity
  have he := mul_le_mul_of_nonneg_left (step_exponential_factor hδ hα)
    (show 0 ≤ C * α / 2 by positivity)
  have hb := mul_le_mul_of_nonneg_right hβ (show 0 ≤ (1 + 5 * Real.sqrt (δ / α)) / 2
    by positivity)
  unfold upperStep lowerStep at *
  nlinarith

def lowerSeq (δ : ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | j + 1 => max 0 (lowerStep δ (lowerSeq δ j))

def upperSeq (δ : ℝ) : ℕ → ℝ
  | 0 => 3 / 2
  | j + 1 => upperStep δ (lowerSeq δ j) (upperSeq δ j)

lemma lowerSeq_nonneg (δ : ℝ) (j : ℕ) : 0 ≤ lowerSeq δ j := by
  cases j with
  | zero => norm_num [lowerSeq]
  | succ j => exact le_max_left _ _

lemma lowerSeq_succ_le_half (δ : ℝ) (j : ℕ) :
    lowerSeq δ (j + 1) ≤ lowerSeq δ j / 2 := by
  have hn := lowerSeq_nonneg δ j
  have ht := Real.sqrt_nonneg (δ / lowerSeq δ j)
  simp only [lowerSeq, max_le_iff]
  unfold lowerStep
  constructor <;> nlinarith

lemma lowerSeq_le_geometric (δ : ℝ) (j : ℕ) :
    lowerSeq δ j ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ j := by
  induction j with
  | zero => simp [lowerSeq]
  | succ j ih =>
      have hs := lowerSeq_succ_le_half δ j
      rw [pow_succ]
      nlinarith

lemma exists_lowerSeq_lt {δ : ℝ} (hδ : 0 < δ) :
    ∃ j, lowerSeq δ j < 100 * δ := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show 0 < 200 * δ by positivity)
    (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨j, lt_of_le_of_lt (lowerSeq_le_geometric δ j) (by linarith)⟩

lemma lowerSeq_succ_eq {δ : ℝ} (hδ : 0 < δ) (j : ℕ)
    (hj : 100 * δ ≤ lowerSeq δ j) :
    lowerSeq δ (j + 1) = lowerStep δ (lowerSeq δ j) :=
  max_eq_right (lowerStep_pos hδ hj).le

lemma upperSeq_nonneg (δ : ℝ) (j : ℕ) : 0 ≤ upperSeq δ j := by
  induction j with
  | zero => norm_num [upperSeq]
  | succ j ih => dsimp only [upperSeq, upperStep]; positivity

lemma upperSeq_ge_geometric (δ : ℝ) (j : ℕ) :
    (3 / 2 : ℝ) * (1 / 2 : ℝ) ^ j ≤ upperSeq δ j := by
  induction j with
  | zero => simp [upperSeq]
  | succ j ih =>
      have hn := upperSeq_nonneg δ j
      have ht := Real.sqrt_nonneg (δ / lowerSeq δ j)
      simp only [upperSeq, upperStep, pow_succ]
      nlinarith

lemma sequence_potential {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (hbefore : ∀ j < n, 100 * δ ≤ lowerSeq δ j) :
    upperSeq δ n ≤ 3 * lowerSeq δ n *
      Real.exp (60 * Real.sqrt (δ / lowerSeq δ n)) := by
  induction n with
  | zero =>
      simp only [lowerSeq, upperSeq]
      have he : 1 ≤ Real.exp (60 * Real.sqrt (δ / (1 / 2))) :=
        Real.one_le_exp (by positivity)
      nlinarith
  | succ n ih =>
      have hprev := ih (fun j hj => hbefore j (Nat.lt_succ_of_lt hj))
      have hα := hbefore n (Nat.lt_succ_self n)
      have hs := step_potential hδ hα (by norm_num : (0 : ℝ) ≤ 3) hprev
      simpa only [upperSeq, lowerSeq_succ_eq hδ n hα] using hs

def selectionConstant : ℝ := 300 * Real.exp 12

lemma selectionConstant_pos : 0 < selectionConstant := by
  unfold selectionConstant
  positivity

/-- An explicit stopping time and uniform endpoint estimates for the LT
iteration starting with norm bounds `1/2` and `3/2`. -/
theorem exists_iteration_stop {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ < 1 / 200) :
    ∃ n : ℕ, 0 < n ∧ (∀ j < n, 100 * δ ≤ lowerSeq δ j) ∧
      25 * δ ≤ lowerSeq δ n ∧ upperSeq δ n ≤ selectionConstant * δ ∧
      (1 / 2 : ℝ) ^ n ≤ selectionConstant * δ := by
  let hex := exists_lowerSeq_lt hδ
  let n := Nat.find hex
  have hend : lowerSeq δ n < 100 * δ := Nat.find_spec hex
  have hbefore : ∀ j < n, 100 * δ ≤ lowerSeq δ j := by
    intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    rw [hn0] at hend
    norm_num [lowerSeq] at hend
    linarith
  have hlower : 25 * δ ≤ lowerSeq δ n := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hp := hbefore k (by omega)
    rw [hk, lowerSeq_succ_eq hδ k hp]
    exact le_trans (by linarith) (lowerStep_bounds hδ hp).1
  have ha : 0 < lowerSeq δ n := lt_of_lt_of_le (by positivity) hlower
  have ht : Real.sqrt (δ / lowerSeq δ n) ≤ 1 / 5 := by
    have hs := Real.sq_sqrt (div_nonneg hδ.le ha.le)
    have hd : δ / lowerSeq δ n ≤ 1 / 25 := (div_le_iff₀ ha).mpr (by linarith)
    nlinarith [Real.sqrt_nonneg (δ / lowerSeq δ n)]
  have he : Real.exp (60 * Real.sqrt (δ / lowerSeq δ n)) ≤ Real.exp 12 :=
    Real.exp_le_exp.mpr (by linarith)
  have hpot := sequence_potential hδ n hbefore
  have hupper : upperSeq δ n ≤ selectionConstant * δ := by
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 3 * lowerSeq δ n by positivity)
    have hd := mul_le_mul_of_nonneg_right hend.le (show 0 ≤ 3 * Real.exp 12 by positivity)
    unfold selectionConstant
    nlinarith
  refine ⟨n, hn, hbefore, hlower, hupper, ?_⟩
  have hg := upperSeq_ge_geometric δ n
  have hz : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

end Tusnady.Frame
