import Tusnady.Literature
import Tusnady.FiniteSamplingAnalysis
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Elementary, unconditional consequences of the exact sampling inputs.

These do not assert the unresolved universal O(D) selection theorem.
In particular the dimension-one theorem below is explicitly indexed by 1.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace Tusnady.LiteratureSampling

variable {X : Type*} [MeasurableSpace X] {D : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]

def squareSum (u : Fin D → X → ℝ) (x : X) : ℝ := ∑ i, u i x ^ 2

lemma squareSum_integrable (u : Fin D → X → ℝ)
    (hint : ∀ i j, Integrable (fun x => u i x * u j x) μ) :
    Integrable (squareSum u) μ := by
  classical
  exact integrable_finset_sum _ (fun i _ => by simpa only [pow_two] using hint i i)

lemma integral_squareSum (u : Fin D → X → ℝ)
    (hint : ∀ i j, Integrable (fun x => u i x * u j x) μ)
    (horth : ∀ i j, (∫ x, u i x * u j x ∂μ) = if i = j then 1 else 0) :
    (∫ x, squareSum u x ∂μ) = D := by
  classical
  simp only [squareSum]
  rw [integral_finset_sum _ (fun i _ => by simpa only [pow_two] using hint i i)]
  simp only [pow_two, horth, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- Condition E with t=1 is saturated almost everywhere, even when it is
only a pointwise upper bound in the statement of the literature theorem. -/
theorem conditionE_saturated_ae (u : Fin D → X → ℝ)
    (hint : ∀ i j, Integrable (fun x => u i x * u j x) μ)
    (horth : ∀ i j, (∫ x, u i x * u j x ∂μ) = if i = j then 1 else 0)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ)) :
    ∀ᵐ x ∂μ, squareSum u x = (D : ℝ) := by
  have hi : Integrable (fun x => (D : ℝ) - squareSum u x) μ :=
    (integrable_const _).sub (squareSum_integrable μ u hint)
  have hn : ∀ x, 0 ≤ (D : ℝ) - squareSum u x := by
    intro x
    exact sub_nonneg.mpr (by simpa only [squareSum, sq_abs] using hE x)
  have hz : (∫ x, (D : ℝ) - squareSum u x ∂μ) = 0 := by
    rw [integral_sub (integrable_const _) (squareSum_integrable μ u hint),
      integral_squareSum μ u hint horth]
    simp
  have ha := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hn) hi).mp hz
  filter_upwards [ha] with x hx
  exact (sub_eq_zero.mp hx).symm

lemma square_le_dimension (u : Fin D → X → ℝ)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ)) (i : Fin D) (x : X) :
    u i x ^ 2 ≤ (D : ℝ) := by
  have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (u j x))
    (Finset.mem_univ i)
  exact hi.trans (by simpa only [sq_abs] using hE x)

/-- Every function in the exact literature interface is genuinely bounded
and belongs to all finite Lp spaces; this discharges LT22 Remark 3.3. -/
lemma conditionE_memLp (u : Fin D → X → ℝ) (humeas : ∀ i, Measurable (u i))
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ)) (i : Fin D) (p : ℝ≥0∞) :
    MemLp (u i) p μ := by
  apply MemLp.of_bound (humeas i).aestronglyMeasurable (Real.sqrt D)
  apply Filter.Eventually.of_forall
  intro x
  have hs := square_le_dimension u hE i x
  rw [Real.norm_eq_abs]
  apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa only [sq_abs, Real.sq_sqrt (Nat.cast_nonneg D)] using hs

lemma integral_combination_abs_sq (u : Fin D → X → ℝ) (humeas : ∀ i, Measurable (u i))
    (horth : ∀ i j, (∫ x, u i x * u j x ∂μ) = if i = j then 1 else 0)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ)) (a : Fin D → ℝ) :
    (∫ x, |∑ i, a i * u i x| ^ 2 ∂μ) = ∑ i, a i ^ 2 := by
  simp only [sq_abs]
  exact FiniteSamplingAnalysis.integral_combination_sq μ u
    (fun i => conditionE_memLp μ u humeas hE i 2) horth a

/-- The exact dimension-one sampling instance with constants all equal
to one, under the original literature hypotheses and no extra premise. -/
theorem sampling_dimension_one (u : Fin 1 → X → ℝ)
    (humeas : ∀ i, Measurable (u i))
    (hint : ∀ i j, Integrable (fun x => u i x * u j x) μ)
    (horth : ∀ i j, (∫ x, u i x * u j x ∂μ) = if i = j then 1 else 0)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (1 : ℝ)) :
    ∃ ξ : Fin 1 → X, ∀ a : Fin 1 → ℝ,
      (∫ x, |∑ i, a i * u i x| ^ 2 ∂μ) =
        (1 / (1 : ℝ)) * ∑ j, |∑ i, a i * u i (ξ j)| ^ 2 := by
  have ha := conditionE_saturated_ae μ u hint horth (by simpa only [Nat.cast_one] using hE)
  obtain ⟨x, hx⟩ := ha.exists
  have hx' : u 0 x ^ 2 = 1 := by simpa [squareSum] using hx
  refine ⟨fun _ => x, fun a => ?_⟩
  rw [integral_combination_abs_sq μ u humeas horth (by simpa only [Nat.cast_one] using hE) a]
  simp only [Fin.sum_univ_one, one_div, inv_one, one_mul, sq_abs, mul_pow, hx', mul_one]

end Tusnady.LiteratureSampling
