import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# The Jensen aggregation in Proposition 6.2

`conditionalEntropy i ω` and `conditionalCorrelation i ω` are explicitly
supplied real functions. Their identification with conditional differential
entropy and conditional CDF correlation is still required in the complete
proof. This module proves both Jensen steps with actual integrals; it does
not assume their final combined conclusion or declare a main theorem.
-/

open MeasureTheory Set
open scoped BigOperators

namespace Tusnady

/-- Finite Jensen for the mean of real exponentials. The positive number
of coordinates is represented by `[Nonempty ι]`. -/
theorem exp_mean_le_mean_exp {ι : Type*} [Fintype ι] [Nonempty ι]
    (h : ι → ℝ) :
    Real.exp ((∑ i, h i) / Fintype.card ι) ≤
      (∑ i, Real.exp (h i)) / Fintype.card ι := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let weight : ι → ℝ := fun _ => 1 / Fintype.card ι
  have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ weight i := by
    intro i _
    dsimp [weight]
    positivity
  have hwone : ∑ i : ι, weight i = 1 := by
    simp [weight, hn.ne']
  have hj := convexOn_exp.map_sum_le (t := Finset.univ)
    (w := weight) (p := h) hw hwone (fun i _ => mem_univ (h i))
  have hmean (f : ι → ℝ) : (∑ i, weight i * f i) =
      (∑ i, f i) / Fintype.card ι := by
    simp only [weight, ← Finset.mul_sum]
    ring
  simpa only [smul_eq_mul, hmean] using hj

/-- The second Jensen step in Prop. 6.2, given the per-coordinate
exponential bound. All scalar inputs remain visible. -/
theorem sum_correlation_of_exp_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (h corr : ι → ℝ) {K : ℝ} (hK : 0 < K)
    (hscalar : ∀ i, Real.exp (h i) ≤ K * corr i) :
    (Fintype.card ι : ℝ) * Real.exp ((∑ i, h i) / Fintype.card ι) / K ≤
      ∑ i, corr i := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hj := (le_div_iff₀ hn).mp (exp_mean_le_mean_exp h)
  have hs : (∑ i, Real.exp (h i)) ≤ K * ∑ i, corr i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hscalar i
  apply (div_le_iff₀ hK).mpr
  nlinarith

/-- The first Jensen step in Prop. 6.2, on an actual probability space. -/
theorem exp_integral_le_integral_exp {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (h : Ω → ℝ)
    (hh : Integrable h μ) (he : Integrable (fun ω => Real.exp (h ω)) μ) :
    Real.exp (∫ ω, h ω ∂μ) ≤ ∫ ω, Real.exp (h ω) ∂μ := by
  exact convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun ω => mem_univ (h ω)) hh he

/-- Both Jensen steps and the chain-rule summation in Prop. 6.2.

The caller must supply actual integrable conditional entropy/correlation
functions and identify them with the chosen random vector. The local
inequality is the scalar conclusion proved in `Tusnady.Gini`, to be
applied to the conditional scalar probability laws. The entropy identity
is an explicit input representing the classical chain rule. -/
theorem entropy_correlation_aggregation {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (conditionalEntropy conditionalCorrelation : ι → Ω → ℝ) {entropy K : ℝ}
    (hK : 0 < K)
    (hh : ∀ i, Integrable (conditionalEntropy i) μ)
    (he : ∀ i, Integrable (fun ω => Real.exp (conditionalEntropy i ω)) μ)
    (hc : ∀ i, Integrable (conditionalCorrelation i) μ)
    (hlocal : ∀ i, ∀ᵐ ω ∂μ,
      Real.exp (conditionalEntropy i ω) ≤ K * conditionalCorrelation i ω)
    (hchain : (∑ i, ∫ ω, conditionalEntropy i ω ∂μ) = entropy) :
    (Fintype.card ι : ℝ) * Real.exp (entropy / Fintype.card ι) / K ≤
      ∑ i, ∫ ω, conditionalCorrelation i ω ∂μ := by
  rw [← hchain]
  apply sum_correlation_of_exp_bounds
    (fun i => ∫ ω, conditionalEntropy i ω ∂μ)
    (fun i => ∫ ω, conditionalCorrelation i ω ∂μ) hK
  intro i
  calc
    Real.exp (∫ ω, conditionalEntropy i ω ∂μ) ≤
        ∫ ω, Real.exp (conditionalEntropy i ω) ∂μ :=
      exp_integral_le_integral_exp (conditionalEntropy i) (hh i) (he i)
    _ ≤ ∫ ω, K * conditionalCorrelation i ω ∂μ :=
      integral_mono_ae (he i) ((hc i).const_mul K) (hlocal i)
    _ = K * ∫ ω, conditionalCorrelation i ω ∂μ := integral_const_mul _ _

end Tusnady
