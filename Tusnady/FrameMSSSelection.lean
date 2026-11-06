import Tusnady.FrameMSSConditional
import Tusnady.FrameRootSelection

/-! # Actual finite MSS realization selection

Successive coordinate choices use genuine conditional product laws.
All convex-combination splitness requirements are discharged by the
proved expected-characteristic-polynomial identity and actual PSD moments.
There is no interlacing or realization-selection assumption.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Tusnady.FrameMSS
open RealRooted.MixedCharacteristic

variable {m n : ℕ} {κ : Type} [Fintype κ]

/-- A positive-probability realization inherits any root bound of the actual expectation. -/
theorem exists_positive_realization_roots_le
    (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ)
    (hpn : ∀ i a, 0 ≤ p i a) (hp : ∀ i, ∑ a, p i a = 1)
    (R : ℝ) (hparent : ∀ r ∈ (expected v p).roots, r ≤ R) :
    ∃ s : Fin m → κ, (∀ i, 0 < p i (s i)) ∧
      ∀ r ∈ (∑ i, Matrix.vecMulVec (v i (s i)) (v i (s i))).charpoly.roots, r ≤ R := by
  classical
  have ha (i : Fin m) : ∃ a, 0 < p i a := by
    by_contra hnone
    push_neg at hnone
    have hh := Finset.sum_nonpos (s := Finset.univ) (fun a _ => hnone a)
    rw [hp i] at hh
    norm_num at hh
  let initial : Fin m → κ := fun i => Classical.choose (ha i)
  have hstage : ∀ k : ℕ, k ≤ m →
      ∃ s : Fin m → κ,
        (∀ i, i.val < k → 0 < p i (s i)) ∧
        ∀ r ∈ (expected v (prefixCondition p k s)).roots, r ≤ R := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨initial, ?_, ?_⟩
        · intro i hi
          omega
        · rw [prefixCondition_zero]
          exact hparent
    | succ k ih =>
        intro hk
        have hkm : k < m := Nat.lt_of_succ_le hk
        let j : Fin m := ⟨k,hkm⟩
        obtain ⟨s,hpos,hroot⟩ := ih (Nat.le_of_succ_le hk)
        let q := prefixCondition p k s
        have hqn : ∀ i a, 0 ≤ q i a := prefixCondition_nonneg p hpn k s
        have hq : ∀ i, ∑ a, q i a = 1 := prefixCondition_normalized p hp k s
        let family : κ → ℝ[X] := fun a => expected v (freeze q j a)
        have hm : ∀ a, (family a).Monic := fun a =>
          expected_monic v _ (freeze_normalized q hq j a)
        have hd : ∀ a, (family a).natDegree = n := fun a =>
          expected_natDegree v _ (freeze_normalized q hq j a)
        have hs : ∀ w : κ → ℝ, (∀ a, 0 ≤ w a) → (∑ a, w a = 1) →
            (FrameRootSelection.mean w family).Splits := by
          intro w hwn hw
          exact conditional_combinations_split v q hqn hq j w hwn hw
        have hmean : FrameRootSelection.mean (q j) family = expected v q :=
          expected_recombine_current v q j
        have hmeanroot : ∀ r ∈ (FrameRootSelection.mean (q j) family).roots, r ≤ R := by
          rw [hmean]
          exact hroot
        obtain ⟨a,hapos,haroot⟩ := FrameRootSelection.exists_pos_weight_roots_le
          (q j) family hm hd (hqn j) (hq j) hs R hmeanroot
        have hapos0 : 0 < p j a := by
          change 0 < prefixCondition p k s j a at hapos
          rwa [prefixCondition_current p hkm s] at hapos
        refine ⟨Function.update s j a, ?_, ?_⟩
        · intro i hi
          by_cases hij : i = j
          · subst i
            simpa using hapos0
          · rw [Function.update_of_ne hij]
            apply hpos i
            have hival : i.val ≠ k := fun h => hij (Fin.ext h)
            omega
        · rw [prefixCondition_next p hkm s a]
          exact haroot
  obtain ⟨s,hpos,hroot⟩ := hstage m le_rfl
  refine ⟨s, fun i => hpos i i.isLt, ?_⟩
  rw [prefixCondition_full, expected_pointProbabilities] at hroot
  exact hroot

/-- The selected outcome has a strictly positive actual product probability. -/
theorem exists_product_positive_realization_roots_le
    (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ)
    (hpn : ∀ i a, 0 ≤ p i a) (hp : ∀ i, ∑ a, p i a = 1)
    (R : ℝ) (hparent : ∀ r ∈ (expected v p).roots, r ≤ R) :
    ∃ s : Fin m → κ, 0 < ∏ i, p i (s i) ∧
      ∀ r ∈ (∑ i, Matrix.vecMulVec (v i (s i)) (v i (s i))).charpoly.roots, r ≤ R := by
  obtain ⟨s,hpos,hroot⟩ := exists_positive_realization_roots_le v p hpn hp R hparent
  exact ⟨s, Finset.prod_pos (fun i _ => hpos i), hroot⟩

end Tusnady.FrameMSS
