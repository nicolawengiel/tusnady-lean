import Tusnady.FrameBasic
import Tusnady.FrameLTNumerics

/-! Actual subset energies, cardinalities, and the smaller-half choice. -/

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Tusnady.Frame

def masked {D M : ℕ} (v : Fin M → Space D) (S : Finset (Fin M))
    (j : Fin M) : Space D := if j ∈ S then v j else 0

lemma energy_masked {D M : ℕ} (v : Fin M → Space D) (S T : Finset (Fin M))
    (w : Space D) : energy (masked v S) T w = energy v (T ∩ S) w := by
  classical
  unfold energy masked
  simp only [apply_ite, inner_zero_right, ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  congr 1

lemma energy_masked_univ {D M : ℕ} (v : Fin M → Space D) (S : Finset (Fin M))
    (w : Space D) : energy (masked v S) Finset.univ w = energy v S w := by
  rw [energy_masked, Finset.univ_inter]

lemma masked_norm_sq_le {D M : ℕ} (v : Fin M → Space D) (S : Finset (Fin M))
    {δ : ℝ} (hδ : 0 ≤ δ) (hv : ∀ j, ‖v j‖ ^ 2 ≤ δ) (j : Fin M) :
    ‖masked v S j‖ ^ 2 ≤ δ := by
  classical
  by_cases hj : j ∈ S <;> simp only [masked, hj, if_true, if_false]
  · exact hv j
  · simpa using hδ

lemma dimension_le_card_subset {D M : ℕ} (v : Fin M → Space D)
    (S : Finset (Fin M)) {a : ℝ} (ha : 0 < a)
    (hl : ∀ w, a * ‖w‖ ^ 2 ≤ energy v S w) : D ≤ S.card := by
  classical
  let T : Space D →ₗ[ℝ] (S → ℝ) := {
    toFun := fun w j => inner ℝ (v j) w
    map_add' := by intro x y; ext j; exact inner_add_right _ _ _
    map_smul' := by intro c x; ext j; simp [inner_smul_right] }
  have hker : ∀ w, T w = 0 → w = 0 := by
    intro w hw
    have hz : energy v S w = 0 := by
      unfold energy
      apply Finset.sum_eq_zero
      intro j hj
      have he : inner ℝ w (v j) = 0 := by
        rw [real_inner_comm]
        exact congrFun hw ⟨j, hj⟩
      rw [he]
      norm_num
    have hnorm : ‖w‖ ^ 2 = 0 := by
      have h := hl w
      rw [hz] at h
      nlinarith [sq_nonneg ‖w‖]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hinj : Function.Injective T := by
    intro w z hwz
    apply sub_eq_zero.mp
    apply hker
    rw [map_sub, hwz, sub_self]
  simpa [Space] using LinearMap.finrank_le_finrank_of_injective hinj

/-- Both pieces of an actual partition satisfy the supplied energy bounds;
choosing the smaller intersection really divides the current cardinality by
two. -/
lemma exists_smaller_piece {D M : ℕ} (v : Fin M → Space D)
    (S T : Finset (Fin M)) (a b : ℝ)
    (hT : ∀ w, a * ‖w‖ ^ 2 ≤ energy (masked v S) T w ∧
      energy (masked v S) T w ≤ b * ‖w‖ ^ 2)
    (hTc : ∀ w, a * ‖w‖ ^ 2 ≤ energy (masked v S) (Finset.univ \ T) w ∧
      energy (masked v S) (Finset.univ \ T) w ≤ b * ‖w‖ ^ 2) :
    ∃ U : Finset (Fin M), U ⊆ S ∧ 2 * (U.card : ℝ) ≤ S.card ∧
      ∀ w, a * ‖w‖ ^ 2 ≤ energy v U w ∧ energy v U w ≤ b * ‖w‖ ^ 2 := by
  classical
  have hsum : ((S ∩ T).card : ℝ) + ((S \ T).card : ℝ) = S.card := by
    exact_mod_cast Finset.card_inter_add_card_sdiff S T
  by_cases hc : 2 * ((S ∩ T).card : ℝ) ≤ S.card
  · refine ⟨S ∩ T, Finset.inter_subset_left, hc, fun w => ?_⟩
    simpa only [energy_masked, Finset.inter_comm] using hT w
  · refine ⟨S \ T, Finset.sdiff_subset, ?_, fun w => ?_⟩
    · linarith
    · have he : (Finset.univ \ T) ∩ S = S \ T := by ext j; simp; tauto
      simpa only [energy_masked, he] using hTc w

end Tusnady.Frame
