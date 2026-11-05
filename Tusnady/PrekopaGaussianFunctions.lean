import Tusnady.PrekopaDecay
import Mathlib.MeasureTheory.Integral.Pi

/-! Continuous positive functions with an integrable Gaussian envelope. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Tusnady.Prekopa

/-- A structural function class preserved by one-coordinate integration. -/
structure GaussianDominated (n : ℕ) (f : (Fin n → ℝ) → ℝ) : Prop where
  continuous : Continuous f
  positive : ∀ x, 0 < f x
  bound : ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
    ∀ x, f x ≤ C * Real.exp (-a * ∑ i, (x i) ^ 2)

def envelope (n : ℕ) (a : ℝ) (x : Fin n → ℝ) : ℝ :=
  Real.exp (-a * ∑ i, (x i) ^ 2)

lemma envelope_eq_product (n : ℕ) (a : ℝ) (x : Fin n → ℝ) :
    envelope n a x = ∏ i, Real.exp (-a * (x i) ^ 2) := by
  rw [envelope, ← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

lemma envelope_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (envelope n a) := by
  have h := Integrable.fintype_prod (ι := Fin n)
    (fun _ => integrable_exp_neg_mul_sq ha)
  simpa only [← envelope_eq_product, ← volume_pi] using h

lemma GaussianDominated.integrable {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : GaussianDominated n f) : Integrable f := by
  obtain ⟨C, a, _, ha, hbound⟩ := hf.bound
  apply ((envelope_integrable n ha).const_mul C).mono' hf.continuous.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs, abs_of_pos (hf.positive x)] using hbound x

lemma envelope_cons (n : ℕ) (a t : ℝ) (x : Fin n → ℝ) :
    envelope (n+1) a (Fin.cons t x) =
      Real.exp (-a * t ^ 2) * envelope n a x := by
  rw [envelope, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [mul_add, Real.exp_add]
  rfl

lemma envelope_le_one (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (x : Fin n → ℝ) :
    envelope n a x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma GaussianDominated.slice_continuous {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) (x : Fin n → ℝ) :
    Continuous (fun t => f (Fin.cons t x)) :=
  hf.continuous.comp ((continuous_id : Continuous (fun t : ℝ => t)).finCons
    (continuous_const : Continuous (fun _ : ℝ => x)))

lemma GaussianDominated.slice_bound {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) : ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ x : Fin n → ℝ, ∀ t : ℝ, f (Fin.cons t x) ≤ C * Real.exp (-a * t ^ 2) := by
  obtain ⟨C,a,hC,ha,hb⟩ := hf.bound
  refine ⟨C,a,hC,ha,fun x t => ?_⟩
  have hb' := hb (Fin.cons t x)
  change f (Fin.cons t x) ≤ C * envelope (n+1) a (Fin.cons t x) at hb'
  rw [envelope_cons, ← mul_assoc] at hb'
  exact hb'.trans (mul_le_of_le_one_right (by positivity) (envelope_le_one n ha.le x))

lemma GaussianDominated.slice_integrable {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) (x : Fin n → ℝ) :
    Integrable (fun t => f (Fin.cons t x)) := by
  obtain ⟨C,a,_,ha,hb⟩ := hf.slice_bound
  exact integrable_of_scalar_gaussian_bound ha (hf.slice_continuous x).aestronglyMeasurable
    (fun t => (hf.positive _).le) (hb x)

lemma GaussianDominated.slice_decay {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) (x : Fin n → ℝ) :
    Tendsto (fun t => f (Fin.cons t x)) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,a,_,ha,hb⟩ := hf.slice_bound
  exact tendsto_zero_of_gaussian_bound ha (fun t => (hf.positive _).le) (hb x)

end Tusnady.Prekopa

namespace Tusnady.Prekopa

def marginal {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ t : ℝ, f (Fin.cons t x)

lemma GaussianDominated.marginal_continuous {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) : Continuous (marginal f) := by
  obtain ⟨C,a,_,ha,hb⟩ := hf.slice_bound
  apply continuous_of_dominated
    (fun x => (hf.slice_continuous x).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun t => ?_)
    ((integrable_exp_neg_mul_sq ha).const_mul C)
    (Eventually.of_forall fun t => ?_)
  · simpa only [Real.norm_eq_abs, abs_of_pos (hf.positive _)] using hb x t
  · exact hf.continuous.comp
      ((continuous_const : Continuous (fun _ : Fin n → ℝ => t)).finCons continuous_id)

lemma GaussianDominated.marginal_positive {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) (x : Fin n → ℝ) : 0 < marginal f x := by
  apply integral_pos_of_integrable_nonneg_nonzero (hf.slice_continuous x)
    (hf.slice_integrable x) (fun t => (hf.positive _).le)
  exact (hf.positive (Fin.cons 0 x)).ne'

lemma GaussianDominated.marginal_bound {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) : ∃ C a : ℝ, 0 < C ∧ 0 < a ∧
      ∀ x, marginal f x ≤ C * envelope n a x := by
  obtain ⟨C,a,hC,ha,hb⟩ := hf.bound
  have hI : 0 < ∫ t : ℝ, Real.exp (-a * t ^ 2) := by
    apply integral_pos_of_integrable_nonneg_nonzero (by fun_prop)
      (integrable_exp_neg_mul_sq ha) (fun t => (Real.exp_pos _).le)
    exact (Real.exp_pos (-a * (0 : ℝ) ^ 2)).ne'
  refine ⟨C * (∫ t : ℝ, Real.exp (-a * t ^ 2)), a, mul_pos hC hI, ha, fun x => ?_⟩
  have hb' : ∀ t : ℝ, f (Fin.cons t x) ≤
      (C * envelope n a x) * Real.exp (-a * t ^ 2) := by
    intro t
    have ht := hb (Fin.cons t x)
    change f (Fin.cons t x) ≤ C * envelope (n+1) a (Fin.cons t x) at ht
    rw [envelope_cons] at ht
    convert ht using 1
    ring
  have hi := integral_mono (hf.slice_integrable x)
    ((integrable_exp_neg_mul_sq ha).const_mul (C * envelope n a x)) hb'
  rw [integral_const_mul] at hi
  exact hi.trans_eq (by ring)

lemma GaussianDominated.marginal {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : GaussianDominated (n+1) f) : GaussianDominated n (marginal f) where
  continuous := hf.marginal_continuous
  positive := hf.marginal_positive
  bound := hf.marginal_bound

end Tusnady.Prekopa
