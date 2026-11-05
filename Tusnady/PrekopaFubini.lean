import Tusnady.PrekopaGaussianFunctions

/-! Fubini and coordinate induction for midpoint Prékopa–Leindler. -/
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace Tusnady.Prekopa

lemma integral_eq_integral_marginal {n : ℕ} {f : (Fin (n+1) → ℝ) → ℝ}
    (hf : Integrable f) : (∫ x, f x) = ∫ x, marginal f x := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hi := (he.integrable_comp_emb e.symm.measurableEmbedding).mpr hf
  have heq := he.integral_comp' f
  change (∫ p : ℝ × (Fin n → ℝ), f (e.symm p)) = ∫ x, f x at heq
  have hcons : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.cons p.1 p.2 := by
    intro p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  change Integrable (fun p : ℝ × (Fin n → ℝ) => f (e.symm p))
    (volume.prod volume) at hi
  simp_rw [hcons] at hi heq
  rw [← heq]
  exact integral_prod_symm _ hi

lemma cons_midpoint {n : ℕ} (t u : ℝ) (x y : Fin n → ℝ) :
    (fun i => (Fin.cons t x i + Fin.cons u y i) / 2) =
      Fin.cons ((t+u)/2) (fun i => (x i+y i)/2) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Midpoint Prékopa–Leindler in arbitrary finite dimension for continuous,
strictly positive functions with Gaussian envelopes. -/
theorem gaussian_midpoint_integral_bound (n : ℕ)
    (f g h : (Fin n → ℝ) → ℝ)
    (hf : GaussianDominated n f) (hg : GaussianDominated n g) (hh : GaussianDominated n h)
    (hmid : ∀ x y, f x * g y ≤ (h (fun i => (x i+y i)/2)) ^ 2) :
    (∫ x, f x) * (∫ x, g x) ≤ (∫ x, h x) ^ 2 := by
  induction n with
  | zero =>
    have hi (q : (Fin 0 → ℝ) → ℝ) : (∫ x, q x) = q 0 := by
      simp only [integral_unique, volume_pi, measureReal_def,
        Measure.pi_empty_univ, ENNReal.toReal_one, one_smul]
      congr 1
      exact Subsingleton.elim _ _
    rw [hi f, hi g, hi h]
    convert hmid 0 0 using 1
    congr 2
    exact Subsingleton.elim _ _
  | succ n ih =>
    have hm : ∀ x y : Fin n → ℝ, marginal f x * marginal g y ≤
        (marginal h (fun i => (x i+y i)/2)) ^ 2 := by
      intro x y
      apply midpoint_integral_bound_of_decay
        (hf.slice_integrable x) (hg.slice_integrable y)
        (hh.slice_integrable (fun i => (x i+y i)/2))
        (hf.slice_continuous x) (hg.slice_continuous y)
        (hf.slice_decay x) (hg.slice_decay y)
        (fun t => hf.positive _) (fun u => hg.positive _)
        (fun v => (hh.positive _).le)
      intro t u
      simpa only [cons_midpoint] using hmid (Fin.cons t x) (Fin.cons u y)
    rw [integral_eq_integral_marginal hf.integrable,
      integral_eq_integral_marginal hg.integrable,
      integral_eq_integral_marginal hh.integrable]
    exact ih (marginal f) (marginal g) (marginal h) hf.marginal hg.marginal hh.marginal hm

end Tusnady.Prekopa
