import Tusnady.LiteratureSamplingGramApprox

/-! Preliminary, unweighted norm discretization with unrestricted list length.
This proves the first finite-approximation stage of LT22; it does not assert
the final linear bound on the number of points. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Tusnady.LiteratureSampling

lemma quadratic_entry_error_le {D : ℕ} (E : Fin D → Fin D → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hE : ∀ i k, |E i k| ≤ δ) (a : Fin D → ℝ) :
    |∑ i, ∑ k, (a i * a k) * E i k| ≤ δ * D * ∑ i, a i ^ 2 := by
  classical
  have hcs : (∑ i, |a i|) ^ 2 ≤ (D : ℝ) * ∑ i, a i ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin D => (1 : ℝ)) (fun i => |a i|)
  calc
    |∑ i, ∑ k, (a i * a k) * E i k|
        ≤ ∑ i, ∑ k, |(a i * a k) * E i k| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ k, |a i| * |a k| * δ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hE i k) (by positivity)
    _ = δ * (∑ i, |a i|) ^ 2 := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ ≤ δ * ((D : ℝ) * ∑ i, a i ^ 2) := mul_le_mul_of_nonneg_left hcs hδ
    _ = _ := by ring

lemma empirical_identity_error_le {X : Type*} {D m : ℕ}
    (u : Fin D → X → ℝ) (ξ : Fin m → X) {δ : ℝ} (hδ : 0 ≤ δ)
    (hG : ∀ i k, |(1 / (m : ℝ)) * (∑ j, u i (ξ j) * u k (ξ j)) -
      (if i = k then 1 else 0)| ≤ δ) (a : Fin D → ℝ) :
    |(1 / (m : ℝ)) * (∑ j, (∑ i, a i * u i (ξ j)) ^ 2) - ∑ i, a i ^ 2|
      ≤ δ * D * ∑ i, a i ^ 2 := by
  classical
  have he : (1 / (m : ℝ)) * (∑ j, (∑ i, a i * u i (ξ j)) ^ 2) =
      FiniteSamplingAnalysis.empirical u (fun _ => 1 / (m : ℝ)) ξ a := by
    unfold FiniteSamplingAnalysis.empirical
    rw [Finset.mul_sum]
  have hid : (∑ i, ∑ k, (a i * a k) * (if i = k then (1 : ℝ) else 0)) =
      ∑ i, a i ^ 2 := by simp [pow_two]
  rw [he, FiniteSamplingAnalysis.empirical_eq_gram]
  conv_lhs => rw [← hid, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  apply quadratic_entry_error_le _ hδ
  intro i k
  simpa only [FiniteSamplingAnalysis.empiricalGram, ← Finset.mul_sum] using hG i k

variable {X : Type*} [MeasurableSpace X] {D : ℕ} (μ : Measure X)
  [IsProbabilityMeasure μ]

/-- A genuine preliminary unweighted sample, valid simultaneously for every
coefficient vector. Its length is finite and can be arbitrarily large; no
linear cardinality bound is included at this stage. -/
theorem exists_finite_norm_approximation (u : Fin D → X → ℝ)
    (hD : 0 < D) (humeas : ∀ i, Measurable (u i))
    (hint : ∀ i k, Integrable (fun x => u i x * u k x) μ)
    (horth : ∀ i k, (∫ x, u i x * u k x ∂μ) = if i = k then 1 else 0)
    (hE : ∀ x, ∑ i, |u i x| ^ 2 ≤ (D : ℝ)) (minimum : ℕ) :
    ∃ m : ℕ, 0 < m ∧ minimum ≤ m ∧ ∃ ξ : Fin m → X,
      ∀ a : Fin D → ℝ,
        (1 / 2 : ℝ) * (∑ i, a i ^ 2) ≤
            (1 / (m : ℝ)) * (∑ j, (∑ i, a i * u i (ξ j)) ^ 2) ∧
        (1 / (m : ℝ)) * (∑ j, (∑ i, a i * u i (ξ j)) ^ 2) ≤
            (3 / 2 : ℝ) * (∑ i, a i ^ 2) := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  let δ : ℝ := 1 / (2 * D)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨m, hm, hmin, ξ, hξ⟩ := exists_finite_gram_approximation μ u humeas hint
    horth hE δ hδ minimum
  refine ⟨m, hm, hmin, ξ, fun a => ?_⟩
  have he := empirical_identity_error_le u ξ hδ.le (fun i k => (hξ i k).le) a
  have hδD : δ * (D : ℝ) = 1 / 2 := by dsimp [δ]; field_simp
  rw [hδD] at he
  obtain ⟨hl, hu⟩ := abs_le.mp he
  constructor <;> linarith

end Tusnady.LiteratureSampling
