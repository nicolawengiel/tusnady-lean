import Tusnady.FiniteSamplingAnalysis
import Tusnady.DistinctApproximation

/-! Preservation of all sampling inequalities while making nodes distinct.
The proof controls the finitely many empirical Gram entries. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace Tusnady.FiniteSamplingAnalysis

variable {X : Type*} [TopologicalSpace X] {D m : ℕ}

lemma empiricalGram_continuous (φ : Fin D → X → ℝ) (a : Fin m → ℝ)
    (hφ : ∀ i, Continuous (φ i)) (i k : Fin D) :
    Continuous (fun Q : Fin m → X => empiricalGram φ a Q i k) := by
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul (((hφ i).comp (continuous_apply j)).mul
    ((hφ k).comp (continuous_apply j)))

theorem distinct_sampling_in_neighborhood
    (hinf : ∀ (x : X) (s : Set X), s ∈ 𝓝 x → s.Infinite)
    (hD : 0 < D) (φ : Fin D → X → ℝ) (hφ : ∀ i, Continuous (φ i))
    (a : Fin m → ℝ) (P : Fin m → X) {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hsample : ∀ b : Fin D → ℝ,
      c * (∑ i, b i ^ 2) ≤ empirical φ a P b ∧
      empirical φ a P b ≤ C * (∑ i, b i ^ 2))
    (V : Set (Fin m → X)) (hV : V ∈ 𝓝 P) :
    ∃ Q ∈ V, Function.Injective Q ∧
      ∀ b : Fin D → ℝ,
        (c / 2) * (∑ i, b i ^ 2) ≤ empirical φ a Q b ∧
        empirical φ a Q b ≤ (2 * C) * (∑ i, b i ^ 2) := by
  classical
  let ε : ℝ := min c C / 2
  let δ : ℝ := ε / D
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hε : 0 < ε := div_pos (lt_min hc hC) (by norm_num)
  have hδ : 0 < δ := div_pos hε hDr
  let U : Set (Fin m → X) :=
    {Q | ∀ i k, |empiricalGram φ a Q i k - empiricalGram φ a P i k| < δ}
  have hUopen : IsOpen U := by
    simp only [U, Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro k
    exact isOpen_Iio.preimage (((empiricalGram_continuous φ a hφ i k).sub continuous_const).abs)
  have hPU : P ∈ U := by simpa [U] using fun (_ _ : Fin D) => hδ
  obtain ⟨Q, hQV, hQ⟩ := DistinctApproximation.exists_injective_in_nhds hinf P
    (U ∩ V) (inter_mem (hUopen.mem_nhds hPU) hV)
  refine ⟨Q, hQV.2, hQ, ?_⟩
  intro b
  have he := empirical_sub_le φ a P Q hδ.le (fun i k => (hQV.1 i k).le) b
  have hδε : δ * (D : ℝ) = ε := by dsimp [δ]; field_simp
  rw [hδε] at he
  have hn : 0 ≤ ∑ i, b i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hec : ε ≤ c / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have heC : ε ≤ C := by dsimp [ε]; linarith [min_le_right c C]
  have hec' := mul_le_mul_of_nonneg_right hec hn
  have heC' := mul_le_mul_of_nonneg_right heC hn
  have hlow := (abs_le.mp he).1
  have hupp := (abs_le.mp he).2
  constructor <;> nlinarith [(hsample b).1, (hsample b).2]

end Tusnady.FiniteSamplingAnalysis
