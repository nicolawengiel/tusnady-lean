import Tusnady.Upper.DyadicFactorizationLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit Gaussian thresholds

Elementary logarithmic estimates for a union bound over `(N+1)^s` orthant
queries. The sample size is positive; the projected dimension may be zero.
The constants in the final square-root estimate depend only on that dimension.
-/
noncomputable section
namespace Tusnady.Upper

/-- The reciprocal scale used for the Gaussian tail budget. -/
def gaussianTailScale (s N : ℕ) : ℝ := 8 * (N : ℝ) * ((N : ℝ)+1)^s

lemma gaussianTailScale_eq_natCast (s N : ℕ) :
    gaussianTailScale s N = (8*N*(N+1)^s : ℕ) := by
  simp [gaussianTailScale]

lemma gaussianTailScale_pos (s N : ℕ) (hN : 0 < N) : 0 < gaussianTailScale s N := by
  unfold gaussianTailScale
  positivity

lemma one_lt_gaussianTailScale (s N : ℕ) (hN : 0 < N) : 1 < gaussianTailScale s N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (1 : ℝ) ≤ ((N : ℝ)+1)^s := one_le_pow₀ (by linarith)
  unfold gaussianTailScale
  nlinarith

lemma log_gaussianTailScale_pos (s N : ℕ) (hN : 0 < N) :
    0 < Real.log (gaussianTailScale s N) :=
  Real.log_pos (one_lt_gaussianTailScale s N hN)

/-- A convenient count estimate with a constant independent of the sample size. -/
lemma log_gaussianTailScale_le (s N : ℕ) (hN : 0 < N) :
    Real.log (gaussianTailScale s N) ≤ ((s : ℝ)+4) * Real.log ((N : ℝ)+2) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ha : (0 : ℝ) < (N : ℝ)+2 := by positivity
  have hbase : (2 : ℝ) ≤ (N : ℝ)+2 := by linarith
  have hpow3 : (8 : ℝ) ≤ ((N : ℝ)+2)^3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 3
    norm_num at this ⊢
    exact this
  have hpow : ((N : ℝ)+1)^s ≤ ((N : ℝ)+2)^s :=
    pow_le_pow_left₀ (by positivity) (by linarith) s
  have hmajor : gaussianTailScale s N ≤ ((N : ℝ)+2)^(s+4) := by
    unfold gaussianTailScale
    calc
      _ ≤ ((N : ℝ)+2)^3 * ((N : ℝ)+2) * ((N : ℝ)+2)^s := by
        exact mul_le_mul
          (mul_le_mul hpow3 (by linarith) hn (by positivity)) hpow
          (by positivity) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ Real.log (((N : ℝ)+2)^(s+4)) :=
      Real.log_le_log (gaussianTailScale_pos s N hN) hmajor
    _ = _ := by rw [Real.log_pow]; push_cast; ring

lemma exp_neg_log_eight_mul (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    Real.exp (-Real.log (8 * (N : ℝ) * (M : ℝ))) = 1 / (8 * (N : ℝ) * (M : ℝ)) := by
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  simp only [one_div]

/-- The two-sided tail union budget, before replacing `M` by the query count. -/
lemma two_mul_card_exp_neg_log (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    2 * (M : ℝ) * Real.exp (-Real.log (8 * (N : ℝ) * (M : ℝ))) =
      1 / (4 * (N : ℝ)) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [exp_neg_log_eight_mul N M hN hM]
  field_simp
  ring

lemma exp_neg_log_gaussianTailScale (s N : ℕ) (hN : 0 < N) :
    Real.exp (-Real.log (gaussianTailScale s N)) = 1 / gaussianTailScale s N := by
  rw [Real.exp_neg, Real.exp_log (gaussianTailScale_pos s N hN)]
  simp only [one_div]

lemma query_tail_union_budget (s N : ℕ) (hN : 0 < N) :
    2 * ((N : ℝ)+1)^s * Real.exp (-Real.log (gaussianTailScale s N)) =
      1 / (4 * (N : ℝ)) := by
  have := two_mul_card_exp_neg_log N ((N+1)^s) hN (by positivity)
  simpa [gaussianTailScale] using this

lemma log_sample_pos (N : ℕ) : 0 < Real.log ((N : ℝ)+2) := by
  apply Real.log_pos
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- Converting a natural logarithm power times its square root into the
half-integer real power used in the statement of the upper bound. -/
lemma log_pow_mul_sqrt (s N : ℕ) :
    (Real.log ((N : ℝ)+2))^s * Real.sqrt (Real.log ((N : ℝ)+2)) =
      (Real.log ((N : ℝ)+2))^((s : ℝ)+(1 : ℝ)/2) := by
  rw [Real.rpow_add (log_sample_pos N), Real.rpow_natCast, Real.sqrt_eq_rpow]

/-- The slab threshold is strictly positive whenever its row bound is. -/
lemma gaussianThreshold_pos (s N : ℕ) (hN : 0 < N) {B : ℝ} (hB : 0 < B) :
    0 < B * Real.sqrt (2 * Real.log (gaussianTailScale s N)) := by
  exact mul_pos hB (Real.sqrt_pos.mpr (mul_pos (by norm_num)
    (log_gaussianTailScale_pos s N hN)))

/-- The exact square appearing in a scalar Gaussian tail estimate. -/
lemma gaussianThreshold_sq (s N : ℕ) (hN : 0 < N) (B : ℝ) :
    (B * Real.sqrt (2 * Real.log (gaussianTailScale s N)))^2 =
      2 * B^2 * Real.log (gaussianTailScale s N) := by
  rw [mul_pow, Real.sq_sqrt (mul_nonneg (by norm_num)
    (log_gaussianTailScale_pos s N hN).le)]
  ring

lemma exp_neg_gaussianThreshold_sq_div (s N : ℕ) (hN : 0 < N)
    {B : ℝ} (hB : B ≠ 0) :
    Real.exp (-(B * Real.sqrt (2 * Real.log (gaussianTailScale s N)))^2 /
      (2 * B^2)) = 1 / gaussianTailScale s N := by
  have heq : -(B * Real.sqrt (2 * Real.log (gaussianTailScale s N)))^2 /
      (2 * B^2) = -Real.log (gaussianTailScale s N) := by
    rw [gaussianThreshold_sq s N hN B]
    field_simp
  rw [heq, exp_neg_log_gaussianTailScale s N hN]

/-- Abstract norm-bound version, convenient when the actual factorization row
norm has already been bounded by `C * log(N+2)^s`. -/
lemma scaled_gaussianThreshold_le (s N : ℕ) (hN : 0 < N) {B C : ℝ}
    (hC : 0 ≤ C)
    (hBC : B ≤ C * (Real.log ((N : ℝ)+2))^s) :
    B * Real.sqrt (2 * Real.log (gaussianTailScale s N)) ≤
      C * Real.sqrt (2 * ((s : ℝ)+4)) *
        (Real.log ((N : ℝ)+2))^((s : ℝ)+(1 : ℝ)/2) := by
  have hlog := log_gaussianTailScale_le s N hN
  have hs : 0 ≤ 2 * ((s : ℝ)+4) := by positivity
  have hroot : Real.sqrt (2 * Real.log (gaussianTailScale s N)) ≤
      Real.sqrt (2 * ((s : ℝ)+4)) * Real.sqrt (Real.log ((N : ℝ)+2)) := by
    calc
      _ ≤ Real.sqrt ((2 * ((s : ℝ)+4)) * Real.log ((N : ℝ)+2)) := by
        apply Real.sqrt_le_sqrt
        nlinarith
      _ = _ := Real.sqrt_mul hs _
  calc
    _ ≤ (C * (Real.log ((N : ℝ)+2))^s) *
        (Real.sqrt (2 * ((s : ℝ)+4)) * Real.sqrt (Real.log ((N : ℝ)+2))) :=
      mul_le_mul hBC hroot (Real.sqrt_nonneg _) (mul_nonneg hC (pow_nonneg (log_sample_pos N).le s))
    _ = _ := by rw [← log_pow_mul_sqrt s N]; ring

/-- The threshold obtained from the explicit dyadic factorization. -/
lemma dyadic_gaussianThreshold_le (s N : ℕ) (hN : 0 < N) :
    (DyadicFactorization.factorConstant s * (Real.log ((N : ℝ)+2))^s) *
        Real.sqrt (2 * Real.log (gaussianTailScale s N)) ≤
      DyadicFactorization.factorConstant s * Real.sqrt (2 * ((s : ℝ)+4)) *
        (Real.log ((N : ℝ)+2))^((s : ℝ)+(1 : ℝ)/2) := by
  apply scaled_gaussianThreshold_le s N hN
  · exact (DyadicFactorization.factorConstant_pos s).le
  · exact le_rfl

end Tusnady.Upper
