import Tusnady.FrameSubset
import Tusnady.FramePartition

/-! The actual smaller-half iteration and its endpoint bounds.
The intermediate generic lemma accepts a concrete halving operation. The
unconditional application uses the separately proved MSS partition theorem.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady.Frame

lemma lowerSeq_le_upperSeq (δ : ℝ) (j : ℕ) : lowerSeq δ j ≤ upperSeq δ j := by
  have hl := lowerSeq_le_geometric δ j
  have hu := upperSeq_ge_geometric δ j
  have hp : 0 ≤ (1 / 2 : ℝ) ^ j := by positivity
  linarith

/-- The finite iteration is proved for an explicitly supplied operation on
actual subsets. This is an intermediate composition lemma, not an asserted
existence theorem for such an operation. -/
theorem exists_iterated_subset {D M : ℕ} (v : Fin M → Space D) {δ : ℝ}
    (hδ : 0 < δ)
    (hhalf : ∀ (S : Finset (Fin M)) (α β : ℝ), 100 * δ ≤ α → α ≤ β →
      (∀ w, α * ‖w‖ ^ 2 ≤ energy v S w ∧ energy v S w ≤ β * ‖w‖ ^ 2) →
      ∃ U : Finset (Fin M), U ⊆ S ∧ 2 * (U.card : ℝ) ≤ S.card ∧
        ∀ w, lowerStep δ α * ‖w‖ ^ 2 ≤ energy v U w ∧
          energy v U w ≤ upperStep δ α β * ‖w‖ ^ 2)
    (hinit : ∀ w, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ energy v Finset.univ w ∧
      energy v Finset.univ w ≤ (3 / 2 : ℝ) * ‖w‖ ^ 2)
    (n : ℕ) (hbefore : ∀ j < n, 100 * δ ≤ lowerSeq δ j) :
    ∃ S : Finset (Fin M), (S.card : ℝ) ≤ M * (1 / 2 : ℝ) ^ n ∧
      ∀ w, lowerSeq δ n * ‖w‖ ^ 2 ≤ energy v S w ∧
        energy v S w ≤ upperSeq δ n * ‖w‖ ^ 2 := by
  classical
  induction n with
  | zero =>
      refine ⟨Finset.univ, by simp, ?_⟩
      simpa only [lowerSeq, upperSeq] using hinit
  | succ n ih =>
      obtain ⟨S, hcard, hS⟩ := ih (fun j hj => hbefore j (Nat.lt_succ_of_lt hj))
      have hα := hbefore n (Nat.lt_succ_self n)
      obtain ⟨U, _hUS, hUcard, hU⟩ := hhalf S (lowerSeq δ n) (upperSeq δ n) hα
        (lowerSeq_le_upperSeq δ n) hS
      refine ⟨U, ?_, ?_⟩
      · rw [pow_succ]
        nlinarith
      · simpa only [lowerSeq_succ_eq hδ n hα, upperSeq] using hU

/-- Cardinality and frame-energy bounds at the actual stopping subset.
The halving argument is explicit here so its eventual application to the
proved MSS construction can be audited independently. -/
theorem exists_small_subset_of_halving {D M : ℕ} (v : Fin M → Space D)
    (hD : 0 < D) (hM : 0 < M) (hmin : 201 * D ≤ M)
    (hhalf : ∀ (S : Finset (Fin M)) (α β : ℝ),
      100 * ((D : ℝ) / M) ≤ α → α ≤ β →
      (∀ w, α * ‖w‖ ^ 2 ≤ energy v S w ∧ energy v S w ≤ β * ‖w‖ ^ 2) →
      ∃ U : Finset (Fin M), U ⊆ S ∧ 2 * (U.card : ℝ) ≤ S.card ∧
        ∀ w, lowerStep ((D : ℝ) / M) α * ‖w‖ ^ 2 ≤ energy v U w ∧
          energy v U w ≤ upperStep ((D : ℝ) / M) α β * ‖w‖ ^ 2)
    (hinit : ∀ w, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ energy v Finset.univ w ∧
      energy v Finset.univ w ≤ (3 / 2 : ℝ) * ‖w‖ ^ 2) :
    ∃ S : Finset (Fin M), D ≤ S.card ∧ (S.card : ℝ) ≤ selectionConstant * D ∧
      ∀ w, 25 * ((D : ℝ) / M) * ‖w‖ ^ 2 ≤ energy v S w ∧
        energy v S w ≤ selectionConstant * ((D : ℝ) / M) * ‖w‖ ^ 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hminR : 201 * (D : ℝ) ≤ M := by exact_mod_cast hmin
  have hδ : 0 < (D : ℝ) / M := div_pos hDR hMR
  have hδsmall : (D : ℝ) / M < 1 / 200 := (div_lt_iff₀ hMR).mpr (by linarith)
  obtain ⟨n, _hn, hbefore, hlower, hupper, hgeom⟩ := exists_iteration_stop hδ hδsmall
  obtain ⟨S, hcard, hS⟩ := exists_iterated_subset v hδ hhalf hinit n hbefore
  have hSbounds : ∀ w, 25 * ((D : ℝ) / M) * ‖w‖ ^ 2 ≤ energy v S w ∧
      energy v S w ≤ selectionConstant * ((D : ℝ) / M) * ‖w‖ ^ 2 := by
    intro w
    exact ⟨(mul_le_mul_of_nonneg_right hlower (sq_nonneg _)).trans (hS w).1,
      (hS w).2.trans (mul_le_mul_of_nonneg_right hupper (sq_nonneg _))⟩
  refine ⟨S, dimension_le_card_subset v S (by positivity : 0 < 25 * ((D : ℝ) / M))
    (fun w => (hSbounds w).1), ?_, hSbounds⟩
  have hc := hcard.trans (mul_le_mul_of_nonneg_left hgeom hMR.le)
  have he : (M : ℝ) * (selectionConstant * ((D : ℝ) / M)) = selectionConstant * D := by
    field_simp
  exact he ▸ hc

/-- Unweighted finite frame selection, using the proved MSS partition and
the explicit finite LT iteration. There is no partition/selection hypothesis
among the inputs of this theorem. -/
theorem exists_small_subset {D M : ℕ} (v : Fin M → Space D)
    (hD : 0 < D) (hM : 0 < M) (hmin : 201 * D ≤ M)
    (hNorm : ∀ j, ‖v j‖ ^ 2 ≤ (D : ℝ) / M)
    (hEnergy : ∀ w, (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ energy v Finset.univ w ∧
      energy v Finset.univ w ≤ (3 / 2 : ℝ) * ‖w‖ ^ 2) :
    ∃ S : Finset (Fin M), D ≤ S.card ∧ (S.card : ℝ) ≤ selectionConstant * D ∧
      ∀ w, 25 * ((D : ℝ) / M) * ‖w‖ ^ 2 ≤ energy v S w ∧
        energy v S w ≤ selectionConstant * ((D : ℝ) / M) * ‖w‖ ^ 2 := by
  have hδ : 0 < (D : ℝ) / M := div_pos (by exact_mod_cast hD) (by exact_mod_cast hM)
  apply exists_small_subset_of_halving v hD hM hmin ?_ hEnergy
  intro S α β hα hβα hS
  have hmasked : ∀ j, ‖masked v S j‖ ^ 2 ≤ (D : ℝ) / M :=
    masked_norm_sq_le v S hδ.le hNorm
  have hmaskedEnergy : ∀ w, α * ‖w‖ ^ 2 ≤ energy (masked v S) Finset.univ w ∧
      energy (masked v S) Finset.univ w ≤ β * ‖w‖ ^ 2 := by
    intro w
    simpa only [energy_masked_univ] using hS w
  obtain ⟨T, hT, hTc⟩ := exists_partition_bounds (masked v S) α β ((D : ℝ) / M)
    hδ hα hβα hmasked hmaskedEnergy
  exact exists_smaller_piece v S T (lowerStep ((D : ℝ) / M) α)
    (upperStep ((D : ℝ) / M) α β) hT hTc

end Tusnady.Frame
