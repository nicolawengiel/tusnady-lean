import Tusnady.LiteratureSamplingFiniteApprox

/-! Genuine finite approximation of the identity covariance, with no
selection axiom. The list length is unrestricted at this preliminary step. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace Tusnady.LiteratureSampling

variable {X : Type*} [MeasurableSpace X] {D : ℕ} (μ : Measure X) [IsProbabilityMeasure μ]

lemma conditionE_product_bound (u : Fin D → X → ℝ)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ)) (i k : Fin D) (x : X) :
    |u i x * u k x| ≤ (D : ℝ) := by
  have hs : (u i x * u k x) ^ 2 ≤ (D : ℝ) ^ 2 := by
    rw [mul_pow, pow_two (D : ℝ)]
    exact mul_le_mul (square_le_dimension u hE i x) (square_le_dimension u hE k x)
      (sq_nonneg _) (Nat.cast_nonneg _)
  exact (sq_le_sq₀ (abs_nonneg _) (Nat.cast_nonneg D)).mp (by simpa only [sq_abs] using hs)

theorem exists_finite_gram_approximation (u : Fin D → X → ℝ)
    (humeas : ∀ i, Measurable (u i))
    (hint : ∀ i k, Integrable (fun x => u i x * u k x) μ)
    (horth : ∀ i k, (∫ x, u i x * u k x ∂μ) = if i = k then 1 else 0)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ))
    (ε : ℝ) (hε : 0 < ε) (minimum : ℕ) :
    ∃ m : ℕ, 0 < m ∧ minimum ≤ m ∧ ∃ ξ : Fin m → X,
      ∀ i k, |(1 / (m : ℝ)) * (∑ j, u i (ξ j) * u k (ξ j)) -
        (if i = k then 1 else 0)| < ε := by
  classical
  let g : (Fin D × Fin D) → X → ℝ := fun p x =>
    u p.1 x * u p.2 x - if p.1 = p.2 then 1 else 0
  have hg : ∀ p, Measurable (g p) := fun p =>
    ((humeas p.1).mul (humeas p.2)).sub measurable_const
  have hb : ∀ p x, |g p x| ≤ (D : ℝ) + 1 := by
    intro p x
    have hi : |(if p.1 = p.2 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    exact (abs_sub _ _).trans (add_le_add (conditionE_product_bound u hE _ _ x) hi)
  have hgp : ∀ p, MemLp (g p) 2 μ := fun p =>
    MemLp.of_bound (hg p).aestronglyMeasurable _ (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hb p x))
  have hz : ∀ p, (∫ x, g p x ∂μ) = 0 := by
    intro p
    rw [show (∫ x, g p x ∂μ) = (∫ x, u p.1 x * u p.2 x ∂μ) -
      (∫ _x, (if p.1 = p.2 then (1 : ℝ) else 0) ∂μ) from
        integral_sub (hint p.1 p.2) (integrable_const _), horth]
    simp
  obtain ⟨m, hm, hmin, ξ, hξ⟩ := exists_simultaneous_empirical_means μ g hg hgp hz
    ((D : ℝ) + 1) (by positivity) hb ε hε minimum
  refine ⟨m, hm, hmin, ξ, fun i k => ?_⟩
  have he : ((∑ j, g (i, k) (ξ j)) / (m : ℝ)) =
      (1 / (m : ℝ)) * (∑ j, u i (ξ j) * u k (ξ j)) - (if i = k then 1 else 0) := by
    dsimp only [g]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [← he]
  exact hξ (i, k)

end Tusnady.LiteratureSampling
