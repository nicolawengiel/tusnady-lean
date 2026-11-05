import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Numerical lower response scale, Main.pdf Proposition 5.6(f)

All constants precede the shell depth parameter. The calculation keeps
the shape count K, shell volume v, and actual number m of sample points
visible. No sampling or manuscript theorem is postulated here.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.ResponseScale

/-- The scale used by the concrete weighted-Gram construction separates
into a fixed positive factor and sqrt(m*v). -/
theorem targetScale_factor (γ c L v m : ℝ) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hL : 0 < L) (_hv : 0 ≤ v) (_hm : 0 ≤ m) :
    Real.sqrt ((γ*v*c)*(m/L)) = Real.sqrt (γ*c/L)*Real.sqrt (m*v) := by
  rw [← Real.sqrt_mul (by positivity : 0 ≤ γ*c/L)]
  congr 1
  field_simp

theorem targetScale_lower (γ c L v m K cN : ℝ) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hL : 0 < L) (hv : 0 ≤ v) (hm : 0 ≤ m) (_hK : 0 ≤ K) (hcN : 0 ≤ cN)
    (hmv : cN*K ≤ m*v) :
    Real.sqrt (γ*c/L)*Real.sqrt cN*Real.sqrt K ≤ Real.sqrt ((γ*v*c)*(m/L)) := by
  rw [targetScale_factor γ c L v m hγ hc hL hv hm, mul_assoc,
    ← Real.sqrt_mul hcN]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmv) (Real.sqrt_nonneg _)

/-- An explicit positive, depth-independent constant. -/
def scaleConstant (t cσ cK : ℝ) : ℝ := t*cσ*cK*Real.sqrt cK/8

lemma scaleConstant_pos (t cσ cK : ℝ) (ht : 0 < t) (hσ : 0 < cσ) (hK : 0 < cK) :
    0 < scaleConstant t cσ cK := by
  unfold scaleConstant
  positivity

/-- Core exponent calculation. In dimension d=n+2, theta=t/sqrt(x^n),
K≥cK*x^(n+1), sigma≥cσ*sqrt K, and v*M≥K imply
s*M≥C*x^(n+1)*sqrt x for every coordinate response s≥v*theta*sigma/8. -/
theorem response_times_card_lower (n : ℕ) (x t cσ cK v M K σ s : ℝ)
    (hx : 0 < x) (ht : 0 < t) (hcσ : 0 < cσ) (hcK : 0 < cK)
    (_hv : 0 ≤ v) (hM : 0 ≤ M) (hK : cK*x^(n+1) ≤ K)
    (hσ : cσ*Real.sqrt K ≤ σ) (hKM : K ≤ v*M)
    (hs : v*(t/Real.sqrt (x^n))*σ/8 ≤ s) :
    scaleConstant t cσ cK*x^(n+1)*Real.sqrt x ≤ s*M := by
  have hxpow : 0 < x^n := pow_pos hx n
  have hroot : 0 < Real.sqrt (x^n) := Real.sqrt_pos.2 hxpow
  have hKpos : 0 < K := lt_of_lt_of_le (mul_pos hcK (pow_pos hx _)) hK
  have hσpos : 0 < σ := lt_of_lt_of_le (mul_pos hcσ (Real.sqrt_pos.2 hKpos)) hσ
  have hsqrt : Real.sqrt cK*(Real.sqrt (x^n)*Real.sqrt x) ≤ Real.sqrt K := by
    calc
      _ = Real.sqrt (cK*x^(n+1)) := by
        rw [pow_succ,Real.sqrt_mul hcK.le,Real.sqrt_mul hxpow.le]
      _ ≤ _ := Real.sqrt_le_sqrt hK
  have hσlow : cσ*Real.sqrt cK*(Real.sqrt (x^n)*Real.sqrt x) ≤ σ := by
    calc
      _ = cσ*(Real.sqrt cK*(Real.sqrt (x^n)*Real.sqrt x)) := by ring
      _ ≤ cσ*Real.sqrt K := mul_le_mul_of_nonneg_left hsqrt hcσ.le
      _ ≤ σ := hσ
  calc
    _ = (cK*x^(n+1))*(t/Real.sqrt (x^n))*
        (cσ*Real.sqrt cK*(Real.sqrt (x^n)*Real.sqrt x))/8 := by
      unfold scaleConstant
      field_simp
    _ ≤ K*(t/Real.sqrt (x^n))*σ/8 := by
      gcongr
    _ ≤ (v*M)*(t/Real.sqrt (x^n))*σ/8 := by
      gcongr
    _ = (v*(t/Real.sqrt (x^n))*σ/8)*M := by ring
    _ ≤ s*M := mul_le_mul_of_nonneg_right hs hM

lemma power_mul_sqrt_eq_rpow (x : ℝ) (hx : 0 < x) (k : ℕ) :
    x^k*Real.sqrt x = x^((k:ℝ)+1/2) := by
  rw [Real.rpow_add hx,Real.rpow_natCast,← Real.sqrt_eq_rpow]

/-- The exponent is exactly d−1/2, not a weakened integer exponent. -/
lemma dimension_power_eq_rpow (d : ℕ) (hd : 1 ≤ d) (x : ℝ) (hx : 0 < x) :
    x^(d-1)*Real.sqrt x = x^((d:ℝ)-1/2) := by
  rw [power_mul_sqrt_eq_rpow x hx]
  congr 1
  rw [Nat.cast_sub hd]
  push_cast
  ring

/-- Dimension-d version of Proposition 5.6(f)'s numerical calculation.
All constants t,cσ,cK are positive and independent of x (hence of h,N). -/
theorem response_times_card_lower_dim (d : ℕ) (hd : 2 ≤ d)
    (x t cσ cK v M K σ s : ℝ) (hx : 0 < x) (ht : 0 < t)
    (hcσ : 0 < cσ) (hcK : 0 < cK) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hK : cK*x^(d-1) ≤ K) (hσ : cσ*Real.sqrt K ≤ σ) (hKM : K ≤ v*M)
    (hs : v*(t/Real.sqrt (x^(d-2)))*σ/8 ≤ s) :
    scaleConstant t cσ cK*x^((d:ℝ)-1/2) ≤ s*M := by
  rw [← dimension_power_eq_rpow d (by omega) x hx]
  rw [show d-1 = (d-2)+1 by omega] at hK ⊢
  simpa only [mul_assoc] using
    response_times_card_lower (d-2) x t cσ cK v M K σ s hx ht hcσ hcK hv hM hK hσ hKM hs

end Tusnady.ResponseScale

namespace Tusnady.ResponseScale

/-- Coordinate formulation with the literal response s=v*lambda*sigma;
the manuscript's lambda≥theta/8 is the only lambda input. -/
theorem coordinate_response_times_card_lower_dim (d : ℕ) (hd : 2 ≤ d)
    (x t cσ cK v M K σ lambda : ℝ) (hx : 0 < x) (ht : 0 < t)
    (hcσ : 0 < cσ) (hcK : 0 < cK) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hK : cK*x^(d-1) ≤ K) (hσ : cσ*Real.sqrt K ≤ σ) (hKM : K ≤ v*M)
    (hlambda : (t/Real.sqrt (x^(d-2)))/8 ≤ lambda) :
    scaleConstant t cσ cK*x^((d:ℝ)-1/2) ≤ (v*lambda*σ)*M := by
  have hσnonneg : 0 ≤ σ := (mul_nonneg hcσ.le (Real.sqrt_nonneg _)).trans hσ
  apply response_times_card_lower_dim d hd x t cσ cK v M K σ (v*lambda*σ)
    hx ht hcσ hcK hv hM hK hσ hKM
  calc
    _ = v*((t/Real.sqrt (x^(d-2)))/8)*σ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlambda hv) hσnonneg

/-- With x=h+1, the implicit constant is fixed before h is chosen. -/
theorem shell_response_times_card_lower (d : ℕ) (hd : 2 ≤ d)
    (t cσ cK : ℝ) (ht : 0 < t) (hcσ : 0 < cσ) (hcK : 0 < cK)
    (h : ℕ) (v M K σ lambda : ℝ) (hv : 0 ≤ v) (hM : 0 ≤ M)
    (hK : cK*((h+1:ℕ):ℝ)^(d-1) ≤ K) (hσ : cσ*Real.sqrt K ≤ σ) (hKM : K ≤ v*M)
    (hlambda : (t/Real.sqrt (((h+1:ℕ):ℝ)^(d-2)))/8 ≤ lambda) :
    scaleConstant t cσ cK*((h+1:ℕ):ℝ)^((d:ℝ)-1/2) ≤ (v*lambda*σ)*M :=
  coordinate_response_times_card_lower_dim d hd _ t cσ cK v M K σ lambda
    (by positivity) ht hcσ hcK hv hM hK hσ hKM hlambda

end Tusnady.ResponseScale
