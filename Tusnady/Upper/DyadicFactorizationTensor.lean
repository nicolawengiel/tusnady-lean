import Tusnady.Upper.DyadicFactorizationTree
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Tensor products and normalized Euclidean factorization of grid orthants. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Tusnady.Upper.DyadicFactorization

abbrev TensorFeature (s L : ℕ) := Fin s → Feature L

def tensorRow {s : ℕ} (L : ℕ) (c : Fin s → ℕ) : EuclideanSpace ℝ (TensorFeature s L) :=
  WithLp.toLp 2 (fun f => ∏ j, row L (c j) (f j))

def tensorColumn {s : ℕ} (L : ℕ) (a : Fin s → ℕ) : EuclideanSpace ℝ (TensorFeature s L) :=
  WithLp.toLp 2 (fun f => ∏ j, column L (a j) (f j))

lemma sum_sq_prod {s L : ℕ} (f : Fin s → Feature L → ℝ) :
    (∑ x : TensorFeature s L, (∏ j, f j (x j))^2) = ∏ j, ∑ x, (f j x)^2 := by
  simp only [← Finset.prod_pow]
  exact (Fintype.prod_sum (fun j x => (f j x)^2)).symm

lemma tensorColumn_norm_sq {s : ℕ} (L : ℕ) (a : Fin s → ℕ) (ha : ∀ j, a j < 2^L) :
    ‖tensorColumn L a‖^2 = ((L+1 : ℕ) : ℝ)^s := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [tensorColumn, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  rw [sum_sq_prod]
  simp only [column_sq_sum L _ (ha _), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma tensorRow_norm_sq_le {s : ℕ} (L : ℕ) (c : Fin s → ℕ) (hc : ∀ j, c j ≤ 2^L) :
    ‖tensorRow L c‖^2 ≤ ((L+1 : ℕ) : ℝ)^s := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [tensorRow, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs]
  rw [sum_sq_prod]
  calc
    _ ≤ ∏ _j : Fin s, ((L+1 : ℕ) : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (fun j _ => row_sq_sum_le L (c j) (hc j))
    _ = _ := by simp

lemma tensor_inner {s : ℕ} (L : ℕ) (c a : Fin s → ℕ)
    (hc : ∀ j, c j ≤ 2^L) (ha : ∀ j, a j < 2^L) :
    inner ℝ (tensorRow L c) (tensorColumn L a) = if ∀ j, a j < c j then 1 else 0 := by
  classical
  simp only [tensorRow, tensorColumn, PiLp.inner_apply, RCLike.inner_apply', conj_trivial,
    PiLp.toLp_apply]
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j (f : Feature L) => row L (c j) f * column L (a j) f)]
  simp only [row_dot_column L _ _ (hc _) (ha _)]
  by_cases h : ∀ j, a j < c j
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨j,hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (not_lt.mpr hj))

def normalization (s L : ℕ) : ℝ := Real.sqrt (((L+1 : ℕ) : ℝ)^s)

def normalizedRow {s : ℕ} (L : ℕ) (c : Fin s → ℕ) : EuclideanSpace ℝ (TensorFeature s L) :=
  normalization s L • tensorRow L c

def normalizedColumn {s : ℕ} (L : ℕ) (a : Fin s → ℕ) : EuclideanSpace ℝ (TensorFeature s L) :=
  (normalization s L)⁻¹ • tensorColumn L a

lemma normalization_pos (s L : ℕ) : 0 < normalization s L := by
  apply Real.sqrt_pos.mpr
  positivity

lemma normalization_sq (s L : ℕ) : (normalization s L)^2 = ((L+1 : ℕ) : ℝ)^s := by
  exact Real.sq_sqrt (by positivity)

lemma normalizedColumn_norm_le {s : ℕ} (L : ℕ) (a : Fin s → ℕ) (ha : ∀ j, a j < 2^L) :
    ‖normalizedColumn L a‖ ≤ 1 := by
  have hpos := normalization_pos s L
  have hsq := normalization_sq s L
  have hcol := tensorColumn_norm_sq L a ha
  have hn : ‖tensorColumn L a‖ = normalization s L := by
    nlinarith [norm_nonneg (tensorColumn L a)]
  rw [normalizedColumn, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos), hn]
  exact (inv_mul_cancel₀ hpos.ne').le

lemma normalizedRow_norm_le {s : ℕ} (L : ℕ) (c : Fin s → ℕ) (hc : ∀ j, c j ≤ 2^L) :
    ‖normalizedRow L c‖ ≤ ((L+1 : ℕ) : ℝ)^s := by
  have hpos := normalization_pos s L
  have hsq := normalization_sq s L
  have hrow := tensorRow_norm_sq_le L c hc
  have hn : ‖tensorRow L c‖ ≤ normalization s L := by
    nlinarith [norm_nonneg (tensorRow L c)]
  rw [normalizedRow, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
  calc
    _ ≤ normalization s L * normalization s L := mul_le_mul_of_nonneg_left hn hpos.le
    _ = _ := by nlinarith

lemma normalized_inner {s : ℕ} (L : ℕ) (c a : Fin s → ℕ)
    (hc : ∀ j, c j ≤ 2^L) (ha : ∀ j, a j < 2^L) :
    inner ℝ (normalizedRow L c) (normalizedColumn L a) =
      if ∀ j, a j < c j then 1 else 0 := by
  have hpos := normalization_pos s L
  rw [normalizedRow, normalizedColumn, inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
  exact tensor_inner L c a hc ha

end Tusnady.Upper.DyadicFactorization
