import Tusnady.Shell
import Tusnady.SmoothedBlockLinear

/-!
# The concrete blocks and positive products

All layers and blocks are actual functions of the actual shell coefficients.
This module defines the manuscript's Q± and W and proves their pointwise
bounds and finite product expansion. Integral normalization is separate.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
open Tusnady.Dyadic

/-- The permitted first-coordinate depths, including the zero block. -/
abbrev BlockIndex (h : ℕ) := {a : Fin (h + 1) // 3 ∣ a.val}

/-- The actual shapes in a block; the distinguished coordinate is explicit. -/
abbrev ShapesInBlock (j : Fin d) (a : BlockIndex h) :=
  {r : Shape d h // r.depth j = a.val.val}

def shapeBlockIndex (j : Fin d) (r : Shape d h) : BlockIndex h :=
  ⟨⟨r.depth j, Nat.lt_succ_of_le (depth_le_shell r j)⟩, r.three_dvd_depth j⟩

/-- The block is the actual multilinear extension of the actual tanh sum. -/
def block (j : Fin d) (a : BlockIndex h) (theta : ℝ) (u : Shell d h → ℝ)
    (x : Point d) : ℝ :=
  Walsh.extension (Walsh.smoothedBlock theta : Walsh.Cube (ShapesInBlock j a) → ℝ)
    (fun r => layer r.val u x)

theorem abs_block_le_one (j : Fin d) (a : BlockIndex h) (theta : ℝ)
    (u : Shell d h → ℝ) (hu : ∀ R, |u R| ≤ 1) (x : Point d) :
    |block j a theta u x| ≤ 1 := by
  apply Walsh.abs_smoothedBlock_extension_le_one
  intro r
  exact abs_layer_le_one r.val u hu x

/-- Each sign gives one of the two genuine positive products. -/
def positiveProduct (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (sigma : Bool) (x : Point d) : ℝ :=
  ∏ a : BlockIndex h, (1 + (Walsh.bitSign sigma / 4) * block j a theta u x)

/-- The actual test function of Main.pdf (3.10). -/
def testFunction (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) (x : Point d) : ℝ :=
  (positiveProduct j theta u true x - positiveProduct j theta u false x) / 2

theorem positive_factor_lower (sigma : Bool) {b : ℝ} (hb : |b| ≤ 1) :
    (3 : ℝ) / 4 ≤ 1 + (Walsh.bitSign sigma / 4) * b := by
  have h := abs_le.mp hb
  cases sigma <;> norm_num [Walsh.bitSign] <;> linarith

theorem positiveProduct_lower (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (sigma : Bool) (x : Point d) :
    ((3 : ℝ) / 4) ^ Fintype.card (BlockIndex h) ≤ positiveProduct j theta u sigma x := by
  have hp := Finset.prod_le_prod
    (s := (Finset.univ : Finset (BlockIndex h)))
    (f := fun _ => ((3 : ℝ) / 4))
    (g := fun a => 1 + (Walsh.bitSign sigma / 4) * block j a theta u x)
    (fun _ _ => by norm_num)
    (fun a _ => positive_factor_lower sigma (abs_block_le_one j a theta u hu x))
  simpa only [positiveProduct, Finset.prod_const, Finset.card_univ] using hp

theorem positiveProduct_pos (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (sigma : Bool) (x : Point d) :
    0 < positiveProduct j theta u sigma x :=
  (pow_pos (by norm_num : (0 : ℝ) < 3 / 4) _).trans_le
    (positiveProduct_lower j theta u hu sigma x)

/-- An explicit finite product expansion, independently of the blocks. -/
theorem product_expansion {α : Type*} [Fintype α] [DecidableEq α]
    (c : ℝ) (B : α → ℝ) :
    (∏ a, (1 + c * B a)) = ∑ S : Finset α, c ^ S.card * ∏ a ∈ S, B a := by
  rw [Finset.prod_one_add]
  simp only [Finset.powerset_univ, Finset.prod_mul_distrib, Finset.prod_const]

/-- W contains exactly products meeting an odd number of blocks. -/
theorem testFunction_odd_expansion (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (x : Point d) :
    testFunction j theta u x =
      ∑ S : Finset (BlockIndex h), if Odd S.card then
        ((1 : ℝ) / 4) ^ S.card * (∏ a ∈ S, block j a theta u x) else 0 := by
  change ((∏ a : BlockIndex h, (1 + ((1 : ℝ) / 4) * block j a theta u x)) -
      (∏ a : BlockIndex h, (1 + ((-1 : ℝ) / 4) * block j a theta u x))) / 2 = _
  rw [show (-1 : ℝ) / 4 = -((1 : ℝ) / 4) by ring]
  rw [product_expansion, product_expansion, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hodd : Odd S.card
  · rw [if_pos hodd, hodd.neg_pow]
    ring
  · have heven : Even S.card := Nat.not_odd_iff_even.mp hodd
    rw [if_neg hodd, heven.neg_pow]
    ring

/-- The actual first-order coefficient attached to one actual shell. -/
def linearCoefficient (j : Fin d) (theta : ℝ) (R : Shell d h) : ℝ :=
  (1 / 4 : ℝ) * Walsh.coefficient
    (Walsh.smoothedBlock theta : Walsh.Cube (ShapesInBlock j (shapeBlockIndex j R.1)) → ℝ)
    {⟨R.1, rfl⟩}

def linearTestFunction (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) (x : Point d) : ℝ :=
  ∑ R : Shell d h, linearCoefficient j theta R * u R * qShell R x

/-- These are the quantitative linear-response bounds from Lemma 3.3,
with only the explicit block-size budget still to be instantiated. -/
theorem linearCoefficient_bounds (j : Fin d) {theta : ℝ} (htheta : 0 ≤ theta)
    (hbudget : ∀ a : BlockIndex h,
      theta ^ 2 * (Fintype.card (ShapesInBlock j a) : ℝ) ≤ (1 : ℝ) / 4)
    (R : Shell d h) : theta / 8 ≤ linearCoefficient j theta R ∧
      linearCoefficient j theta R ≤ theta / 4 := by
  have hb := Walsh.smoothedBlock_linear_interval htheta
    (hbudget (shapeBlockIndex j R.1)) (⟨R.1, rfl⟩ : ShapesInBlock j (shapeBlockIndex j R.1))
  unfold linearCoefficient
  constructor <;> nlinarith

end Tusnady.Witness
