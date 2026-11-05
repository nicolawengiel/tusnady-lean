import Tusnady.OneFunctionExtension

/-! Elementary finite quadratic forms of an actual orthonormal family. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.FiniteSamplingAnalysis

variable {α : Type*} {D m : ℕ}

lemma integral_combination_sq [MeasurableSpace α] (μ : Measure α) (φ : Fin D → α → ℝ)
    (hφ : ∀ i, MemLp (φ i) 2 μ)
    (horth : ∀ i j, (∫ x, φ i x * φ j x ∂μ) = if i = j then 1 else 0)
    (b : Fin D → ℝ) :
    (∫ x, (∑ i, b i * φ i x) ^ 2 ∂μ) = ∑ i, b i ^ 2 := by
  classical
  have hi : ∀ i j, Integrable (fun x => (b i * b j) * (φ i x * φ j x)) μ :=
    fun i j => ((hφ i).integrable_mul (hφ j)).const_mul _
  have he : (fun x => (∑ i, b i * φ i x) ^ 2) =
      (fun x => ∑ i, ∑ j, (b i * b j) * (φ i x * φ j x)) := by
    funext x
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j), integral_const_mul, horth]
  simp [pow_two]

def empirical (φ : Fin D → α → ℝ) (a : Fin m → ℝ) (P : Fin m → α)
    (b : Fin D → ℝ) : ℝ := ∑ j, a j * (∑ i, b i * φ i (P j)) ^ 2

def empiricalGram (φ : Fin D → α → ℝ) (a : Fin m → ℝ) (P : Fin m → α)
    (i k : Fin D) : ℝ := ∑ j, a j * (φ i (P j) * φ k (P j))

lemma empirical_eq_gram (φ : Fin D → α → ℝ) (a : Fin m → ℝ) (P : Fin m → α)
    (b : Fin D → ℝ) :
    empirical φ a P b = ∑ i, ∑ k, (b i * b k) * empiricalGram φ a P i k := by
  classical
  unfold empirical empiricalGram
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Entrywise continuity controls every coefficient vector at once. -/
lemma empirical_sub_le (φ : Fin D → α → ℝ) (a : Fin m → ℝ) (P Q : Fin m → α)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hPQ : ∀ i k, |empiricalGram φ a Q i k - empiricalGram φ a P i k| ≤ δ)
    (b : Fin D → ℝ) :
    |empirical φ a Q b - empirical φ a P b| ≤ δ * D * ∑ i, b i ^ 2 := by
  classical
  have hcs : (∑ i, |b i|) ^ 2 ≤ (D : ℝ) * ∑ i, b i ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin D => (1 : ℝ))
      (fun i => |b i|)
  rw [empirical_eq_gram, empirical_eq_gram, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    |∑ i, ∑ k, (b i * b k) * (empiricalGram φ a Q i k - empiricalGram φ a P i k)|
      ≤ ∑ i, ∑ k, |(b i * b k) * (empiricalGram φ a Q i k - empiricalGram φ a P i k)| := by
        apply (Finset.abs_sum_le_sum_abs _ _).trans
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ k, |b i| * |b k| * δ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hPQ i k) (by positivity)
    _ = δ * (∑ i, |b i|) ^ 2 := by
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      rw [← Finset.sum_mul]
      ring
    _ ≤ δ * ((D : ℝ) * ∑ i, b i ^ 2) := mul_le_mul_of_nonneg_left hcs hδ
    _ = _ := by ring

/-- A positive lower sampling inequality forces at least as many nodes as
the actual dimension. Repeated nodes cannot evade this rank argument. -/
theorem dimension_le_sample_count (φ : Fin D → α → ℝ) (a : Fin m → ℝ)
    (P : Fin m → α) {c : ℝ} (hc : 0 < c)
    (hlower : ∀ b : Fin D → ℝ, c * (∑ i, b i ^ 2) ≤ empirical φ a P b) : D ≤ m := by
  classical
  let T : (Fin D → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    Fintype.linearCombination ℝ (fun i => fun j => φ i (P j))
  have hT : ∀ b j, T b j = ∑ i, b i * φ i (P j) := by
    intro b j
    simp [T, Fintype.linearCombination_apply, Finset.sum_apply]
  have hker : ∀ b, T b = 0 → b = 0 := by
    intro b hb
    have he : empirical φ a P b = 0 := by
      unfold empirical
      simp_rw [← hT, hb]
      simp
    have hs : ∑ i, b i ^ 2 = 0 := by
      have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (b i))
      have hl := hlower b
      rw [he] at hl
      nlinarith
    funext i
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => sq_nonneg (b j))
      (Finset.mem_univ i)
    rw [hs] at hi
    exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))
  have hinj : Function.Injective T := by
    intro b b' hb
    have hz : T (b - b') = 0 := by rw [map_sub, hb, sub_self]
    exact sub_eq_zero.mp (hker (b - b') hz)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

end Tusnady.FiniteSamplingAnalysis
