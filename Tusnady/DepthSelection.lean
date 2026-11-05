import Tusnady.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# A logarithmic admissible shell depth for every large cardinality

For convenience the proof uses the explicit depth
3 floor(log N/(6 log 2)), rather than the largest admissible depth.
It has the same required logarithmic size and leaves room for the
polynomial construction factor. No discrepancy estimate is assumed here.
-/
noncomputable section
open Filter
open scoped Topology
namespace Tusnady

/-- Positive natural logarithm of two, fixed independently of dimension. -/
lemma log_two_pos : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)

lemma real_two_pow_eq_exp (h : ℕ) : (2:ℝ)^h = Real.exp (Real.log 2*(h:ℝ)) := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]

/-- Exponential room eventually absorbs any fixed polynomial and constant. -/
theorem eventually_polynomial_le_two_pow (k : ℕ) (C : ℝ) (hC : 0 < C) :
    ∃ h0 : ℕ, ∀ h : ℕ, h0 ≤ h → C*((h:ℝ)+1)^k ≤ (2:ℝ)^h := by
  have he := (isLittleO_pow_exp_pos_mul_atTop k log_two_pos).bound
    (show (0:ℝ)<1/(2*C) by positivity)
  have ht : Tendsto (fun h : ℕ => (h:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hh := ht.eventually he
  obtain ⟨h0,hh0⟩ := eventually_atTop.mp hh
  refine ⟨h0, ?_⟩
  intro h hge
  have hb := hh0 h hge
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity : (0:ℝ)≤(h:ℝ)+1) k),
    abs_of_pos (Real.exp_pos _)] at hb
  have heq : Real.exp (Real.log 2*((h:ℝ)+1)) = (2:ℝ)^h*2 := by
    rw [mul_add, mul_one, Real.exp_add, ← real_two_pow_eq_exp,
      Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [heq] at hb
  have hm := mul_le_mul_of_nonneg_left hb hC.le
  calc
    _ ≤ C * ((1/(2*C))*((2:ℝ)^h*2)) := hm
    _ = (2:ℝ)^h := by field_simp

/-- A deterministic positive-multiple-of-three depth once N is large. -/
def cardinalityDepth (N : ℕ) : ℕ :=
  3*⌊Real.log (N:ℝ)/(6*Real.log 2)⌋₊

lemma cardinalityDepth_three_dvd (N : ℕ) : 3 ∣ cardinalityDepth N := dvd_mul_right _ _

/-- Explicit power and logarithm comparisons at every depth with at least
one floor step. -/
lemma cardinalityDepth_size {N : ℕ} (hN : 1 ≤ N)
    (hf : 1 ≤ ⌊Real.log (N:ℝ)/(6*Real.log 2)⌋₊) :
    (2:ℝ)^(2*cardinalityDepth N) ≤ (N:ℝ) ∧
      Real.log (N:ℝ)/(4*Real.log 2) ≤ (cardinalityDepth N:ℝ)+1 := by
  let f := ⌊Real.log (N:ℝ)/(6*Real.log 2)⌋₊
  have hlog : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hden : (0:ℝ)<6*Real.log 2 := by have := log_two_pos; positivity
  have hden4 : (0:ℝ)<4*Real.log 2 := by have := log_two_pos; positivity
  have hlo := (le_div_iff₀ hden).mp
    (Nat.floor_le (div_nonneg hlog hden.le))
  have hhi := (div_lt_iff₀ hden).mp (Nat.lt_floor_add_one (Real.log (N:ℝ)/(6*Real.log 2)))
  have hfR : (1:ℝ) ≤ (f:ℝ) := by exact_mod_cast hf
  have hc : (cardinalityDepth N:ℝ) = 3*(f:ℝ) := by simp [cardinalityDepth, f]
  constructor
  · rw [real_two_pow_eq_exp]
    apply (Real.exp_le_exp.mpr (show Real.log 2*((2*cardinalityDepth N:ℕ):ℝ) ≤ Real.log (N:ℝ) by
      push_cast
      rw [hc]
      dsimp [f] at hc ⊢
      nlinarith)).trans_eq
    exact Real.exp_log (by exact_mod_cast (show 0<N by omega))
  · apply (div_le_iff₀ hden4).mpr
    rw [hc]
    have hp : 0 ≤ Real.log 2*((f:ℝ)-1) := mul_nonneg log_two_pos.le (by linarith)
    change Real.log (N:ℝ) < ((f:ℝ)+1)*(6*Real.log 2) at hhi
    nlinarith

/-- Every sufficiently large cardinality admits a positive allowed depth,
large enough for any fixed construction threshold and with logarithmic
size. All constants are chosen before N. -/
theorem admissible_depth_for_cardinality (k hmin : ℕ) (C : ℝ) (hC : 0<C) :
    ∃ N0 : ℕ, 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      0 < cardinalityDepth N ∧ 3 ∣ cardinalityDepth N ∧ hmin ≤ cardinalityDepth N ∧
      C*((cardinalityDepth N:ℝ)+1)^k*(2:ℝ)^(cardinalityDepth N) ≤ (N:ℝ) ∧
      Real.log (N:ℝ)/(4*Real.log 2) ≤ (cardinalityDepth N:ℝ)+1 := by
  obtain ⟨h0,hh0⟩ := eventually_polynomial_le_two_pow k C hC
  let H := max h0 (max hmin 1)
  have hHt : Tendsto (fun N : ℕ => Real.log (N:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp (hHt.eventually
    (eventually_ge_atTop (6*Real.log 2*(H:ℝ))))
  refine ⟨max N0 1, le_max_right _ _, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := (le_max_right N0 1).trans hN
  have hlog := hN0 N ((le_max_left N0 1).trans hN)
  have hden : (0:ℝ)<6*Real.log 2 := by have := log_two_pos; positivity
  have hf : H ≤ ⌊Real.log (N:ℝ)/(6*Real.log 2)⌋₊ := by
    apply Nat.le_floor
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  have hH1 : 1 ≤ H := (le_max_right hmin 1).trans (le_max_right h0 _)
  have hh : H ≤ cardinalityDepth N := by unfold cardinalityDepth; omega
  obtain ⟨hpow,hsize⟩ := cardinalityDepth_size hN1 (hH1.trans hf)
  refine ⟨by omega, cardinalityDepth_three_dvd N,
    (le_max_left hmin 1).trans ((le_max_right h0 _).trans hh), ?_, hsize⟩
  calc
    _ ≤ (2:ℝ)^(cardinalityDepth N)*(2:ℝ)^(cardinalityDepth N) :=
      mul_le_mul_of_nonneg_right (hh0 _ ((le_max_left h0 _).trans hh)) (by positivity)
    _ = (2:ℝ)^(2*cardinalityDepth N) := by rw [← pow_add]; congr 1; omega
    _ ≤ (N:ℝ) := hpow

end Tusnady
