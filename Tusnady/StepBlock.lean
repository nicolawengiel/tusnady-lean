import Tusnady.ShellIntegrals

/-!
# Cancellation for concrete three-bit step blocks

The normalization uses only actual dyadic partitions and the vanishing
zeroth moment of q_I. In particular no martingale or conditional-mean
property is postulated.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace Tusnady.Witness
open Tusnady.DyadicFunctions

/-- One concrete one-dimensional block with arbitrary coefficients. -/
def stepBlock (a : ℕ) (z : Fin (2^a) → ℝ) (t : ℝ) : ℝ :=
  ∑ i, z i * qI a i t

lemma qI_integrable_unit (a : ℕ) (i : Fin (2^a)) :
    Integrable (qI a i) Tusnady.Haar.unitMeasure := by
  exact ((qBase_integrable.comp_div (ne_of_gt (dyadicLength_pos a))).comp_sub_right
    (dyadicLeft a i)).restrict

lemma stepBlock_measurable (a : ℕ) (z : Fin (2^a) → ℝ) :
    Measurable (stepBlock a z) := by
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul (measurable_qI a i)

lemma stepBlock_integrable (a : ℕ) (z : Fin (2^a) → ℝ) :
    Integrable (stepBlock a z) Tusnady.Haar.unitMeasure := by
  exact integrable_finset_sum _ fun i _ => (qI_integrable_unit a i).const_mul (z i)

lemma stepBlock_on_interval (a : ℕ) (z : Fin (2^a) → ℝ)
    (i : Fin (2^a)) {t : ℝ} (ht : t ∈ dyadicInterval a i) :
    stepBlock a z t = z i * qI a i t := by
  classical
  unfold stepBlock
  rw [Finset.sum_eq_single i]
  · intro k _ hki
    have hnot : t ∉ dyadicInterval a k := fun hk =>
      Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth a k i hki) hk ht
    rw [qI_zero_outside _ _ _ hnot, mul_zero]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

lemma abs_stepBlock_le_one (a : ℕ) (z : Fin (2^a) → ℝ)
    (hz : ∀ i, |z i| ≤ 1) (t : ℝ) : |stepBlock a z t| ≤ 1 := by
  classical
  by_cases ht : t ∈ Ico (0:ℝ) 1
  · obtain ⟨i, hi, _⟩ := Tusnady.Haar.existsUnique_unit_interval a t ht
    rw [stepBlock_on_interval _ _ i hi, abs_mul]
    have hq : |qI a i t| = 1 := by
      change |q (dyadicLeft a i) (dyadicLength a) t| = 1
      rw [abs_q _ _ _ (dyadicLength_pos a)]
      exact Set.indicator_of_mem hi _
    rw [hq, mul_one]
    exact hz i
  · have hzero : stepBlock a z t = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [qI_zero_outside a i t (fun hi => ht (dyadicInterval_subset_unit a i hi)), mul_zero]
    rw [hzero]
    norm_num

lemma prod_stepBlock_integrable {α : Type*} (S : Finset α) (a : α → ℕ)
    (z : (b : α) → Fin (2^(a b)) → ℝ) (hz : ∀ b i, |z b i| ≤ 1) :
    Integrable (fun t => ∏ b ∈ S, stepBlock (a b) (z b) t) Tusnady.Haar.unitMeasure := by
  apply Integrable.of_bound
    (Finset.measurable_prod _ fun b _ => stepBlock_measurable _ _).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro t
  rw [Real.norm_eq_abs, Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
    (fun b _ => abs_stepBlock_le_one _ _ (hz b) t)

lemma stepBlock_constant_on_finer (a b : ℕ) (hab : a+3 ≤ b)
    (z : Fin (2^a) → ℝ) (i : Fin (2^b)) :
    ∃ c : ℝ, EqOn (stepBlock a z) (fun _ => c) (dyadicInterval b i) := by
  classical
  choose c hc using fun k : Fin (2^a) => qI_constant_on_finer a b hab k i
  refine ⟨∑ k, z k * c k, ?_⟩
  intro t ht
  exact Finset.sum_congr rfl fun k _ => congrArg (z k * ·) (hc k ht)

lemma integral_unit_qI (a : ℕ) (i : Fin (2^a)) :
    (∫ t, qI a i t ∂Tusnady.Haar.unitMeasure) = 0 := by
  rw [Tusnady.Haar.integral_unitMeasure]
  simpa only [pow_zero, mul_one] using integral_unit_qI_moment a i 0 (by omega)

/-- Any function constant on all parent intervals cancels against their
three-bit Walsh block. No measurability condition on that auxiliary
function is needed: the resulting products are actual constant multiples
of integrable q_I's. -/
theorem integral_mul_stepBlock_eq_zero (a : ℕ) (z : Fin (2^a) → ℝ)
    (g : ℝ → ℝ)
    (hg : ∀ i : Fin (2^a), ∃ c : ℝ, EqOn g (fun _ => c) (dyadicInterval a i)) :
    (∫ t, g t * stepBlock a z t ∂Tusnady.Haar.unitMeasure) = 0 := by
  classical
  choose c hc using hg
  have heq (i : Fin (2^a)) (t : ℝ) :
      g t * (z i * qI a i t) = (c i * z i) * qI a i t := by
    by_cases ht : t ∈ dyadicInterval a i
    · rw [hc i ht]
      ring
    · rw [qI_zero_outside _ _ _ ht]
      ring
  have hf : (fun t => g t * stepBlock a z t) =
      (fun t => ∑ i, (c i*z i)*qI a i t) := by
    funext t
    simp only [stepBlock, Finset.mul_sum, heq]
  rw [hf, integral_finset_sum]
  · simp_rw [integral_const_mul, integral_unit_qI, mul_zero]
    simp
  · intro i _
    exact (qI_integrable_unit a i).const_mul _

end Tusnady.Witness

namespace Tusnady.Witness
open Tusnady.DyadicFunctions

/-- A finite product of functions constant on an interval is constant there. -/
lemma finiteProduct_eqOn_constant {α : Type*} (S : Finset α)
    (F : α → ℝ → ℝ) (I : Set ℝ) (t0 : ℝ) (ht0 : t0 ∈ I)
    (hF : ∀ a ∈ S, ∃ c : ℝ, EqOn (F a) (fun _ => c) I) :
    EqOn (fun t => ∏ a ∈ S, F a t) (fun _ => ∏ a ∈ S, F a t0) I := by
  intro t ht
  apply Finset.prod_congr rfl
  intro a ha
  obtain ⟨c, hc⟩ := hF a ha
  exact (hc ht).trans (hc ht0).symm

end Tusnady.Witness
