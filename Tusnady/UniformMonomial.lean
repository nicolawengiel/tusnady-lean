import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Actual product-uniform squarefree monomials and Hilbert Parseval

The measure is the product of the normalized Lebesgue laws on `[-1,1]`.
The first and second scalar moments, mixed-monomial orthogonality, and
finite Hilbert-valued Parseval identity are proved for this actual law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace ENNReal
namespace Tusnady.UniformMonomial

def scalarLaw : Measure ℝ := ProbabilityTheory.cond volume (Icc (-1 : ℝ) 1)

instance scalarLaw_probability : IsProbabilityMeasure scalarLaw := by
  apply cond_isProbabilityMeasure_of_finite
  · norm_num [Real.volume_Icc]
  · norm_num [Real.volume_Icc]

def cubeLaw (α : Type*) [Fintype α] : Measure (α → ℝ) :=
  Measure.pi (fun _ : α => scalarLaw)

instance cubeLaw_probability (α : Type*) [Fintype α] : IsProbabilityMeasure (cubeLaw α) := by
  unfold cubeLaw
  infer_instance

theorem scalar_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂scalarLaw) = (1 / 2 : ℝ) * ∫ x in (-1 : ℝ)..1, f x := by
  unfold scalarLaw ProbabilityTheory.cond
  rw [integral_smul_measure, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  norm_num [Real.volume_Icc]

theorem scalar_first_moment : (∫ x : ℝ, x ∂scalarLaw) = 0 := by
  rw [scalar_integral, integral_id]
  norm_num

theorem scalar_second_moment : (∫ x : ℝ, x ^ 2 ∂scalarLaw) = 1 / 3 := by
  rw [scalar_integral, integral_pow]
  norm_num

theorem ae_cube (α : Type*) [Fintype α] :
    ∀ᵐ u ∂cubeLaw α, ∀ i : α, |u i| ≤ 1 := by
  apply ae_all_iff.mpr
  intro i
  have heval : (cubeLaw α).map (fun u => u i) = scalarLaw :=
    (measurePreserving_eval (fun _ : α => scalarLaw) i).map_eq
  have hscalar : ∀ᵐ x ∂scalarLaw, |x| ≤ 1 := by
    filter_upwards [ae_cond_mem (μ := volume) measurableSet_Icc] with x hx
    exact abs_le.mpr hx
  have hmap : ∀ᵐ x ∂(cubeLaw α).map (fun u => u i), |x| ≤ 1 := by
    rw [heval]
    exact hscalar
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable
    (isClosed_le continuous_abs continuous_const).measurableSet).mp hmap

def monomial {α : Type*} (S : Finset α) (u : α → ℝ) : ℝ := ∏ i ∈ S, u i

theorem monomial_eq_product {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (u : α → ℝ) :
    monomial S u = ∏ i : α, if i ∈ S then u i else 1 := by
  simp [monomial, Finset.prod_ite_mem]

theorem monomial_continuous {α : Type*} (S : Finset α) : Continuous (monomial S) := by
  exact continuous_finset_prod S (fun i _ => continuous_apply i)

theorem monomial_abs_le_one {α : Type*} (S : Finset α) (u : α → ℝ)
    (hu : ∀ i, |u i| ≤ 1) : |monomial S u| ≤ 1 := by
  rw [monomial, Finset.abs_prod]
  exact Finset.prod_le_one (fun i _ => abs_nonneg _) (fun i _ => hu i)

theorem monomial_integrable {α : Type*} [Fintype α] (S : Finset α) :
    Integrable (monomial S) (cubeLaw α) := by
  apply Integrable.of_bound (monomial_continuous S).measurable.aestronglyMeasurable 1
  filter_upwards [ae_cube α] with u hu
  exact monomial_abs_le_one S u hu

theorem monomial_product_integrable {α : Type*} [Fintype α] (S T : Finset α) :
    Integrable (fun u => monomial S u * monomial T u) (cubeLaw α) := by
  apply Integrable.of_bound ((monomial_continuous S).mul (monomial_continuous T)).measurable.aestronglyMeasurable 1
  filter_upwards [ae_cube α] with u hu
  rw [Real.norm_eq_abs, abs_mul]
  exact (mul_le_mul (monomial_abs_le_one S u hu) (monomial_abs_le_one T u hu)
    (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem monomial_mixed_moment {α : Type*} [Fintype α] [DecidableEq α]
    (S T : Finset α) :
    (∫ u, monomial S u * monomial T u ∂cubeLaw α) =
      if S = T then (1 / 3 : ℝ) ^ S.card else 0 := by
  have hp (u : α → ℝ) : monomial S u * monomial T u =
      ∏ i : α, (if i ∈ S then u i else 1) * (if i ∈ T then u i else 1) := by
    rw [monomial_eq_product, monomial_eq_product, Finset.prod_mul_distrib]
  simp_rw [hp]
  rw [show cubeLaw α = Measure.pi (fun _ : α => scalarLaw) from rfl,
    integral_fintype_prod_eq_prod (fun i (x : ℝ) =>
      (if i ∈ S then x else 1) * (if i ∈ T then x else 1))]
  by_cases hST : S = T
  · subst T
    simp only [ite_true]
    have hfactor (i : α) :
        (∫ x : ℝ, (if i ∈ S then x else 1) * (if i ∈ S then x else 1) ∂scalarLaw) =
          if i ∈ S then (1 / 3 : ℝ) else 1 := by
      by_cases hi : i ∈ S
      · simpa only [if_pos hi, ← sq] using scalar_second_moment
      · simp [hi]
    simp_rw [hfactor]
    simp [Finset.prod_ite_mem]
  · simp only [if_neg hST]
    obtain ⟨i, hi⟩ : ∃ i : α, (i ∈ S ∧ i ∉ T) ∨ (i ∉ S ∧ i ∈ T) := by
      by_contra h
      push_neg at h
      exact hST (Finset.ext (fun i => ⟨(h i).1, fun hi => by
        by_contra hn
        exact (h i).2 hn hi⟩))
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    rcases hi with ⟨hiS, hiT⟩ | ⟨hiS, hiT⟩ <;>
      simpa only [hiS, hiT, ↓reduceIte, mul_one, one_mul] using scalar_first_moment

theorem monomial_mean {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α) :
    (∫ u, monomial S u ∂cubeLaw α) = if S = ∅ then 1 else 0 := by
  have h := monomial_mixed_moment S ∅
  by_cases hS : S = ∅
  · subst S
    simp [monomial]
  · simpa only [monomial, Finset.prod_empty, mul_one, if_neg hS] using h

/-- Finite Hilbert-valued Parseval identity for distinct squarefree
monomials under the actual product-uniform coefficient measure. The
vectors need not be mutually orthogonal. -/
theorem finite_parseval {α G E : Type*} [Fintype α] [DecidableEq α]
    [Fintype G] [DecidableEq G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : G → Finset α) (hm : Function.Injective m) (v : G → E) :
    (∫ u, ‖∑ g : G, monomial (m g) u • v g‖ ^ 2 ∂cubeLaw α) =
      ∑ g : G, (1 / 3 : ℝ) ^ (m g).card * ‖v g‖ ^ 2 := by
  have hexpand (u : α → ℝ) : ‖∑ g : G, monomial (m g) u • v g‖ ^ 2 =
      ∑ g : G, ∑ h : G,
        (monomial (m g) u * monomial (m h) u) * inner ℝ (v g) (v h) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro g _
    apply Finset.sum_congr rfl
    intro h _
    rw [real_inner_comm (v h) (v g)]
    ring
  have hprod (g h : G) : Integrable
      (fun u => (monomial (m g) u * monomial (m h) u) * inner ℝ (v g) (v h))
      (cubeLaw α) :=
    (monomial_product_integrable (m g) (m h)).mul_const _
  simp_rw [hexpand]
  rw [integral_finset_sum Finset.univ (fun g _ =>
    integrable_finset_sum Finset.univ (fun h _ => hprod g h))]
  apply Finset.sum_congr rfl
  intro g _
  rw [integral_finset_sum Finset.univ (fun h _ => hprod g h)]
  simp_rw [integral_mul_const, monomial_mixed_moment, hm.eq_iff]
  simp [real_inner_self_eq_norm_sq]

/-- Coefficient form of the same identity, matching Main.pdf (4.6). -/
theorem finite_parseval_weighted {α G E : Type*} [Fintype α] [DecidableEq α]
    [Fintype G] [DecidableEq G] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (m : G → Finset α) (hm : Function.Injective m) (c : G → ℝ) (v : G → E) :
    (∫ u, ‖∑ g : G, (c g * monomial (m g) u) • v g‖ ^ 2 ∂cubeLaw α) =
      ∑ g : G, c g ^ 2 * (1 / 3 : ℝ) ^ (m g).card * ‖v g‖ ^ 2 := by
  have heq (u : α → ℝ) : (∑ g : G, (c g * monomial (m g) u) • v g) =
      ∑ g : G, monomial (m g) u • (c g • v g) := by
    apply Finset.sum_congr rfl
    intro g _
    rw [smul_smul, mul_comm]
  simp_rw [heq]
  rw [finite_parseval m hm]
  apply Finset.sum_congr rfl
  intro g _
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

end Tusnady.UniformMonomial
