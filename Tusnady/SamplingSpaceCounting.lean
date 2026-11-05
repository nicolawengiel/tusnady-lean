import Tusnady.SamplingSpaceSparse
import Mathlib.Algebra.Field.GeomSum

/-!
# Elementary weighted counting of the actual sparse-cross levels

The count uses the total level and all but one coordinate. It gives the
manuscript's polynomial-exponential dimension bounds without assuming a
stars-and-bars formula or a dimension estimate.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

def levelEnergy (d H : ℕ) : ℝ := ∑ ℓ : Levels d H, (2 : ℝ) ^ (∑ k, levelDepth ℓ k)

/-- Encode a positive-dimensional level by its total and tail coordinates. -/
def levelEncode (k H : ℕ) (ℓ : Levels (k + 1) H) :
    Fin (H + 1) × (Fin k → Fin (H + 1)) :=
  (⟨∑ i, levelDepth ℓ i, Nat.lt_succ_of_le ℓ.property⟩, fun i => ℓ.val i.succ)

theorem levelEncode_injective (k H : ℕ) : Function.Injective (levelEncode k H) := by
  intro ℓ m h
  have ht := congrArg (fun p => p.1.val) h
  have htail := congrArg Prod.snd h
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply Fin.ext
    simp only [levelEncode, Fin.sum_univ_succ, levelDepth] at ht
    have hs : (∑ j : Fin k, (ℓ.val j.succ).val) = ∑ j : Fin k, (m.val j.succ).val := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg Fin.val (congrFun htail j)
    omega
  · exact congrFun htail j

/-- The weighted level sum is at most the unrestricted total/tail sum. -/
theorem levelEnergy_upper (k H : ℕ) :
    levelEnergy (k + 1) H ≤ (2 : ℝ) ^ (H + 1) * (H + 1 : ℕ) ^ k := by
  classical
  let f : Fin (H + 1) × (Fin k → Fin (H + 1)) → ℝ := fun p => (2 : ℝ) ^ p.1.val
  have heq : levelEnergy (k + 1) H =
      ∑ p ∈ Finset.univ.image (levelEncode k H), f p := by
    rw [Finset.sum_image]
    · rfl
    · intro ℓ _ m _ h
      exact levelEncode_injective k H h
  have hbound : levelEnergy (k + 1) H ≤ ∑ p, f p := by
    rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro p _ _
    exact pow_nonneg (by norm_num) _
  have hgeom : (∑ b : Fin (H + 1), (2 : ℝ) ^ b.val) ≤ (2 : ℝ) ^ (H + 1) := by
    rw [Fin.sum_univ_eq_sum_range, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
    norm_num
  calc
    levelEnergy (k + 1) H ≤ ∑ p, f p := hbound
    _ = (∑ b : Fin (H + 1), (2 : ℝ) ^ b.val) * (H + 1 : ℕ) ^ k := by
      rw [Fintype.sum_prod_type]
      simp [f, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ ≤ (2 : ℝ) ^ (H + 1) * (H + 1 : ℕ) ^ k :=
      mul_le_mul_of_nonneg_right hgeom (by positivity)

lemma lowerTail_sum_le (k H : ℕ) (t : Fin k → Fin (H / (k + 1) + 1)) :
    (∑ i, (t i).val) ≤ H := by
  have hs : (∑ i, (t i).val) ≤ k * (H / (k + 1)) := by
    calc
      _ ≤ ∑ _i : Fin k, H / (k + 1) :=
        Finset.sum_le_sum fun i _ => Nat.le_of_lt_succ (t i).isLt
      _ = _ := by simp
  have hd : (k + 1) * (H / (k + 1)) ≤ H := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self H (k + 1)
  exact hs.trans ((Nat.mul_le_mul_right (H / (k + 1)) (Nat.le_succ k)).trans hd)

/-- A full grid in all tail coordinates gives distinct level vectors
whose total level is exactly H. -/
def topLevel (k H : ℕ) (t : Fin k → Fin (H / (k + 1) + 1)) : Levels (k + 1) H :=
  ⟨Fin.cons ⟨H - ∑ i, (t i).val, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    (fun i => ⟨(t i).val, (t i).isLt.trans_le (Nat.succ_le_succ (Nat.div_le_self H (k + 1)))⟩), by
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    exact (Nat.sub_add_cancel (lowerTail_sum_le k H t)).le⟩

theorem topLevel_total (k H : ℕ) (t : Fin k → Fin (H / (k + 1) + 1)) :
    (∑ i, levelDepth (topLevel k H t) i) = H := by
  simp only [topLevel, levelDepth, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact Nat.sub_add_cancel (lowerTail_sum_le k H t)

theorem topLevel_injective (k H : ℕ) : Function.Injective (topLevel k H) := by
  intro t u h
  funext i
  apply Fin.ext
  exact congrArg (fun ℓ : Levels (k + 1) H => (ℓ.val i.succ).val) h

/-- The top-level grid provides the polynomial lower factor. -/
theorem levelEnergy_lower_grid (k H : ℕ) :
    (2 : ℝ) ^ H * (H / (k + 1) + 1 : ℕ) ^ k ≤ levelEnergy (k + 1) H := by
  classical
  have heq : (∑ ℓ ∈ Finset.univ.image (topLevel k H),
      (2 : ℝ) ^ (∑ i, levelDepth ℓ i)) =
      (2 : ℝ) ^ H * (H / (k + 1) + 1 : ℕ) ^ k := by
    rw [Finset.sum_image]
    · simp [topLevel_total]
      ring
    · intro t _ u _ h
      exact topLevel_injective k H h
  rw [← heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro ℓ _ _
  positivity

/-- Explicit positive-dimension lower bound for the weighted count. -/
theorem levelEnergy_lower (k H : ℕ) :
    (1 / ((k + 1 : ℕ) : ℝ) ^ k) * (2 : ℝ) ^ H * ((H + 1 : ℕ) : ℝ) ^ k ≤
      levelEnergy (k + 1) H := by
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  have hnat : H + 1 ≤ (k + 1) * (H / (k + 1) + 1) :=
    Nat.succ_le_of_lt (Nat.lt_mul_div_succ H (Nat.succ_pos k))
  have hr : ((H + 1 : ℕ) : ℝ) / (k + 1 : ℕ) ≤ (H / (k + 1) + 1 : ℕ) := by
    apply (div_le_iff₀ hk).mpr
    exact_mod_cast (show H + 1 ≤ (H / (k + 1) + 1) * (k + 1) by simpa only [Nat.mul_comm] using hnat)
  have hp : (((H + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) ^ k ≤ ((H / (k + 1) + 1 : ℕ) : ℝ) ^ k := by
    exact pow_le_pow_left₀ (by positivity) hr k
  calc
    (1 / ((k + 1 : ℕ) : ℝ) ^ k) * (2 : ℝ) ^ H * ((H + 1 : ℕ) : ℝ) ^ k =
        (2 : ℝ) ^ H * (((H + 1 : ℕ) : ℝ) / (k + 1 : ℕ)) ^ k := by
      rw [div_pow]
      ring
    _ ≤ (2 : ℝ) ^ H * ((H / (k + 1) + 1 : ℕ) : ℝ) ^ k :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ levelEnergy (k + 1) H := levelEnergy_lower_grid k H

theorem tensorIndex_card_bounds {d : ℕ} (ℓ : Fin d → ℕ) :
    2 ^ (∑ k, ℓ k) ≤ Fintype.card (TensorIndex ℓ) ∧
      Fintype.card (TensorIndex ℓ) ≤ 2 ^ d * 2 ^ (∑ k, ℓ k) := by
  rw [tensorIndex_card]
  have hlo : (∏ k, 2 ^ (ℓ k)) ≤ ∏ k, Module.finrank ℝ (detailSpace (ℓ k)) := by
    apply Finset.prod_le_prod
    · intro k _
      exact Nat.zero_le _
    · intro k _
      exact (detailSpace_finrank_bounds (ℓ k)).1
  have hhi : (∏ k, Module.finrank ℝ (detailSpace (ℓ k))) ≤ ∏ k, 2 * 2 ^ (ℓ k) := by
    apply Finset.prod_le_prod
    · intro k _
      exact Nat.zero_le _
    · intro k _
      exact (detailSpace_finrank_bounds (ℓ k)).2
  constructor
  · simpa only [Finset.prod_pow_eq_pow_sum] using hlo
  · simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum] using hhi

/-- The actual sparse-cross dimension is comparable to its weighted
multi-level count. -/
theorem sparseSpace_dimension_energy_bounds (d H : ℕ) :
    levelEnergy d H ≤ (Module.finrank ℝ (sparseSpace d H) : ℝ) ∧
      (Module.finrank ℝ (sparseSpace d H) : ℝ) ≤ (2 : ℝ) ^ d * levelEnergy d H := by
  rw [sparseSpace_finrank, Fintype.card_sigma, Nat.cast_sum]
  unfold levelEnergy
  constructor
  · apply Finset.sum_le_sum
    intro ℓ _
    exact_mod_cast (tensorIndex_card_bounds (levelDepth ℓ)).1
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ _
    exact_mod_cast (tensorIndex_card_bounds (levelDepth ℓ)).2

/-- Main.pdf Lemma 5.1(b), with explicit constants in positive dimension.
For d=k+1 the lower constant is d^(-k), and the upper constant 2^(k+2).
Both are independent of H. -/
theorem sparseSpace_dimension_bounds (k H : ℕ) :
    (1 / ((k + 1 : ℕ) : ℝ) ^ k) * (2 : ℝ) ^ H * ((H + 1 : ℕ) : ℝ) ^ k ≤
        (Module.finrank ℝ (sparseSpace (k + 1) H) : ℝ) ∧
      (Module.finrank ℝ (sparseSpace (k + 1) H) : ℝ) ≤
        (2 : ℝ) ^ (k + 2) * (2 : ℝ) ^ H * ((H + 1 : ℕ) : ℝ) ^ k := by
  have he := sparseSpace_dimension_energy_bounds (k + 1) H
  constructor
  · exact (levelEnergy_lower k H).trans he.1
  · calc
      _ ≤ (2 : ℝ) ^ (k + 1) * levelEnergy (k + 1) H := he.2
      _ ≤ (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (H + 1) * ((H + 1 : ℕ) : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (levelEnergy_upper k H) (by positivity)
      _ = _ := by simp only [pow_succ]; ring

theorem sparseSpace_finrank_pos (d H : ℕ) (hd : 0 < d) :
    0 < Module.finrank ℝ (sparseSpace d H) := by
  cases d with
  | zero => omega
  | succ k =>
    have h := (sparseSpace_dimension_bounds k H).1
    have hlo : (0 : ℝ) < (1 / ((k + 1 : ℕ) : ℝ) ^ k) * (2 : ℝ) ^ H * ((H + 1 : ℕ) : ℝ) ^ k := by
      positivity
    have hp : (0 : ℝ) < (Module.finrank ℝ (sparseSpace (k + 1) H) : ℝ) := hlo.trans_le h
    exact_mod_cast hp

end Tusnady.SamplingSpace
