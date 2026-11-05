import Tusnady.ShapeCounting
import Tusnady.SamplingDomainBasis

/-! The actual sparse-space dimension and shell-cardinality are comparable
with explicit constants depending only on dimension. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
open Tusnady.SamplingSpace

def sizeLowerConstant (d : ℕ) : ℝ := 1/(d:ℝ)^(d-1)
def sizeUpperConstant (d : ℕ) : ℝ :=
  (2:ℝ)^(4*d+1)*((3*d+1:ℕ):ℝ)^(d-1)*((3*d:ℕ):ℝ)^(d-1)

lemma sizeLowerConstant_pos {d : ℕ} (hd : 0<d) : 0<sizeLowerConstant d := by
  unfold sizeLowerConstant
  have h : (0:ℝ)<d := by exact_mod_cast hd
  positivity

lemma sizeUpperConstant_pos {d : ℕ} (hd : 0<d) : 0<sizeUpperConstant d := by
  unfold sizeUpperConstant
  have h : 0<3*d := by omega
  have hR : (0:ℝ)<3*d := by exact_mod_cast h
  positivity

/-- Literal comparison of the actual finite dimensions. -/
theorem sparseDimension_shell_comparison (k h : ℕ) (hh : 3 ∣ h) :
    sizeLowerConstant (k+1)*(Fintype.card (Shell (k+1) h):ℝ) ≤
      (sparseDimension (k+1) (h+3*(k+1)):ℝ) ∧
    (sparseDimension (k+1) (h+3*(k+1)):ℝ) ≤
      sizeUpperConstant (k+1)*(Fintype.card (Shell (k+1) h):ℝ) := by
  classical
  have hdims := sparseSpace_dimension_bounds k (h+3*(k+1))
  rw [sparseSpace_finrank] at hdims
  have hshapeU : (Fintype.card (Dyadic.Shape (k+1) h):ℝ) ≤ ((h:ℝ)+1)^k := by
    exact_mod_cast Dyadic.card_shape_le k h
  have hshapeL := Dyadic.card_shape_lower k h hh
  have hpoly : ((h:ℝ)+1)^k ≤ ((3*(k+1):ℕ):ℝ)^k *
      (Fintype.card (Dyadic.Shape (k+1) h):ℝ) := by
    have hp : (0:ℝ)<((3*(k+1):ℕ):ℝ)^k := by positivity
    have heq : ((3:ℝ)*(k+1:ℕ))^k = ((3*(k+1):ℕ):ℝ)^k := by norm_cast
    rw [heq] at hshapeL
    have he : ((h:ℝ)+1)^k / ((3*(k+1):ℕ):ℝ)^k ≤
        (Fintype.card (Dyadic.Shape (k+1) h):ℝ) := by
      simpa only [one_div, ← div_eq_inv_mul, Nat.cast_add, Nat.cast_one] using hshapeL
    simpa only [mul_comm] using (div_le_iff₀ hp).mp he
  have hH : (h+3*(k+1)+1:ℕ) ≤ (3*(k+1)+1)*(h+1) := by nlinarith
  have hpowH : ((h+3*(k+1)+1:ℕ):ℝ)^k ≤
      ((3*(k+1)+1:ℕ):ℝ)^k * ((h:ℝ)+1)^k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast hH
  rw [card_shell]
  push_cast
  unfold sizeLowerConstant sizeUpperConstant
  simp only [Nat.add_sub_cancel_right]
  constructor
  · calc
      _ = ((1/((k+1:ℕ):ℝ)^k)*(2:ℝ)^h)*
          (Fintype.card (Dyadic.Shape (k+1) h):ℝ) := by ring
      _ ≤ (1/((k+1:ℕ):ℝ)^k)*(2:ℝ)^h*((h:ℝ)+1)^k :=
        mul_le_mul_of_nonneg_left hshapeU (by positivity)
      _ ≤ (1/((k+1:ℕ):ℝ)^k)*(2:ℝ)^(h+3*(k+1))*((h+3*(k+1)+1:ℕ):ℝ)^k := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega)
        · apply pow_le_pow_left₀ (by positivity)
          exact_mod_cast (show h+1 ≤ h+3*(k+1)+1 by omega)
        · positivity
        · positivity
      _ ≤ _ := hdims.1
  · calc
      _ ≤ (2:ℝ)^(k+2)*(2:ℝ)^(h+3*(k+1))*((h+3*(k+1)+1:ℕ):ℝ)^k := hdims.2
      _ ≤ (2:ℝ)^(k+2)*(2:ℝ)^(h+3*(k+1))*
          (((3*(k+1)+1:ℕ):ℝ)^k*(((3*(k+1):ℕ):ℝ)^k*
            (Fintype.card (Dyadic.Shape (k+1) h):ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact hpowH.trans (mul_le_mul_of_nonneg_left hpoly (by positivity))
      _ = _ := by
        have hexp : (2:ℝ)^(k+2)*(2:ℝ)^(h+3*(k+1)) =
            (2:ℝ)^(4*(k+1)+1)*(2:ℝ)^h := by
          rw [← pow_add, ← pow_add]
          congr 1
          omega
        rw [hexp]
        ring

theorem sparseDimension_shell_comparison_dim (d h : ℕ) (hd : 0<d) (hh : 3 ∣ h) :
    sizeLowerConstant d*(Fintype.card (Shell d h):ℝ) ≤
      (sparseDimension d (h+3*d):ℝ) ∧
    (sparseDimension d (h+3*d):ℝ) ≤
      sizeUpperConstant d*(Fintype.card (Shell d h):ℝ) := by
  cases d with
  | zero => omega
  | succ k => exact sparseDimension_shell_comparison k h hh

theorem sample_count_shell_upper (d h m : ℕ) (hd : 0<d) (hh : 3 ∣ h)
    (Cs : ℝ) (hCs : 0≤Cs)
    (hm : (m:ℝ) ≤ Cs*sparseDimension d (h+3*d)) :
    (m:ℝ) ≤ (Cs*sizeUpperConstant d)*(Fintype.card (Shell d h):ℝ) := by
  calc
    _ ≤ Cs*sparseDimension d (h+3*d) := hm
    _ ≤ Cs*(sizeUpperConstant d*(Fintype.card (Shell d h):ℝ)) :=
      mul_le_mul_of_nonneg_left (sparseDimension_shell_comparison_dim d h hd hh).2 hCs
    _ = _ := by ring

lemma card_shell_pos (d h : ℕ) (hd : 0<d) (hh : 3 ∣ h) :
    0<Fintype.card (Shell d h) := by
  cases d with
  | zero => omega
  | succ k =>
    have hl := Dyadic.card_shape_lower k h hh
    have hp : (0:ℝ)<(Fintype.card (Dyadic.Shape (k+1) h):ℝ) :=
      (show (0:ℝ)<(1/((3:ℝ)*(k+1:ℕ))^k)*(h+1:ℕ)^k by positivity).trans_le hl
    rw [card_shell]
    exact Nat.mul_pos (by exact_mod_cast hp) (by positivity)

end Tusnady.Witness
