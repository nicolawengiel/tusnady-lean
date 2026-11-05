import Tusnady.BlockSlice
import Tusnady.StepProduct

/-!
# Normalization of the actual positive products

Main.pdf Lemma 3.2. The one-coordinate cancellation is derived from
concrete step blocks. Fubini then gives the actual cube integrals.
-/
noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace Tusnady.Witness

lemma measurable_layer (r : Dyadic.Shape d h) (u : Shell d h → ℝ) :
    Measurable (layer r u) := by
  exact Finset.measurable_sum _ fun c _ => measurable_const.mul (measurable_qShell _)

lemma measurable_block (j : Fin d) (a : BlockIndex h) (theta : ℝ)
    (u : Shell d h → ℝ) : Measurable (block j a theta u) := by
  unfold block Walsh.extension
  apply Finset.measurable_sum
  intro S _
  exact measurable_const.mul (Finset.measurable_prod _ fun r _ => measurable_layer _ _)

lemma measurable_positiveProduct (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (sigma : Bool) : Measurable (positiveProduct j theta u sigma) := by
  exact Finset.measurable_prod _ fun a _ =>
    measurable_const.add (measurable_const.mul (measurable_block j a theta u))

lemma measurable_testFunction (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) :
    Measurable (testFunction j theta u) :=
  ((measurable_positiveProduct j theta u true).sub
    (measurable_positiveProduct j theta u false)).div_const 2

lemma positive_factor_abs_upper (sigma : Bool) {b : ℝ} (hb : |b| ≤ 1) :
    |1 + (Walsh.bitSign sigma / 4) * b| ≤ (5:ℝ)/4 := by
  have h := abs_le.mp hb
  rw [abs_le]
  cases sigma <;> norm_num [Walsh.bitSign] <;> constructor <;> linarith

lemma abs_positiveProduct_upper (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (sigma : Bool) (x : Point d) :
    |positiveProduct j theta u sigma x| ≤
      ((5:ℝ)/4)^Fintype.card (BlockIndex h) := by
  unfold positiveProduct
  rw [Finset.abs_prod]
  have hp := Finset.prod_le_prod
    (s := (Finset.univ : Finset (BlockIndex h)))
    (f := fun a => |1 + (Walsh.bitSign sigma / 4)*block j a theta u x|)
    (g := fun _ => ((5:ℝ)/4))
    (fun _ _ => abs_nonneg _)
    (fun a _ => positive_factor_abs_upper sigma (abs_block_le_one j a theta u hu x))
  simpa only [Finset.prod_const, Finset.card_univ] using hp

lemma integrable_positiveProduct (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (sigma : Bool) :
    Integrable (positiveProduct j theta u sigma) (Haar.cubeMeasure d) := by
  apply Integrable.of_bound (measurable_positiveProduct j theta u sigma).aestronglyMeasurable
    (((5:ℝ)/4)^Fintype.card (BlockIndex h))
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]
    exact abs_positiveProduct_upper j theta u hu sigma x

/-- The actual product has integral one in the distinguished coordinate,
for every fixed choice of all the other coordinates. -/
theorem integral_positiveProduct_slice (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (sigma : Bool) (x : Point d) :
    (∫ t, positiveProduct j theta u sigma (Function.update x j t)
      ∂Haar.unitMeasure) = 1 := by
  classical
  calc
    _ = ∫ t, (∏ a : BlockIndex h, (1+(Walsh.bitSign sigma/4)*
        stepBlock a.val.val (sliceCoefficients j a theta u x) t)) ∂Haar.unitMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with t ht
      exact Finset.prod_congr rfl fun a _ => congrArg
        (fun b => 1+(Walsh.bitSign sigma/4)*b) (block_slice_eq_stepBlock j a theta u x ht)
    _ = 1 := integral_positive_stepProduct _ _ (sliceCoefficients_bound j · theta u hu x)

/-- Generic finite-dimensional Fubini bridge for a normalized coordinate. -/
lemma integral_cube_of_normalized_slices {n : ℕ} (j : Fin (n+1))
    (f : Point (n+1) → ℝ) (hf : Integrable f (Haar.cubeMeasure (n+1)))
    (hslice : ∀ x : Point (n+1),
      (∫ t, f (Function.update x j t) ∂Haar.unitMeasure) = 1) :
    (∫ x, f x ∂Haar.cubeMeasure (n+1)) = 1 := by
  let mp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (n+1) => Haar.unitMeasure) j).symm
  have hg : Integrable (fun p : ℝ × Point n => f (j.insertNth p.1 p.2))
      (Haar.unitMeasure.prod (Haar.cubeMeasure n)) := by
    exact (mp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hf
  calc
    _ = ∫ p : ℝ × Point n, f (j.insertNth p.1 p.2)
        ∂(Haar.unitMeasure.prod (Haar.cubeMeasure n)) := by
      exact (mp.integral_comp' f).symm
    _ = ∫ v : Point n, ∫ t, f (j.insertNth t v) ∂Haar.unitMeasure
        ∂Haar.cubeMeasure n := integral_prod_symm _ hg
    _ = ∫ _v : Point n, (1:ℝ) ∂Haar.cubeMeasure n := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v
      have hh := hslice (j.insertNth 0 v)
      simpa only [Fin.update_insertNth] using hh
    _ = 1 := by simp

/-- Main.pdf Lemma 3.2: both actual positive products have integral one. -/
theorem integral_positiveProduct {n : ℕ} (j : Fin (n+1)) (theta : ℝ)
    (u : Shell (n+1) h → ℝ) (hu : ∀ R, |u R| ≤ 1) (sigma : Bool) :
    (∫ x, positiveProduct j theta u sigma x ∂Haar.cubeMeasure (n+1)) = 1 := by
  exact integral_cube_of_normalized_slices j _
    (integrable_positiveProduct j theta u hu sigma)
    (integral_positiveProduct_slice j theta u hu sigma)

lemma integrable_testFunction (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) :
    Integrable (testFunction j theta u) (Haar.cubeMeasure d) :=
  ((integrable_positiveProduct j theta u hu true).sub
    (integrable_positiveProduct j theta u hu false)).div_const 2

/-- Main.pdf Lemma 3.2, its L1 conclusion for each positive product. -/
theorem integral_abs_positiveProduct {n : ℕ} (j : Fin (n+1)) (theta : ℝ)
    (u : Shell (n+1) h → ℝ) (hu : ∀ R, |u R| ≤ 1) (sigma : Bool) :
    (∫ x, |positiveProduct j theta u sigma x| ∂Haar.cubeMeasure (n+1)) = 1 := by
  simp_rw [abs_of_pos (positiveProduct_pos j theta u hu sigma _)]
  exact integral_positiveProduct j theta u hu sigma

lemma abs_testFunction_le_products (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (x : Point d) :
    |testFunction j theta u x| ≤
      (positiveProduct j theta u true x + positiveProduct j theta u false x)/2 := by
  unfold testFunction
  rw [abs_div, show |(2:ℝ)|=2 by norm_num]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ |positiveProduct j theta u true x|+|positiveProduct j theta u false x| :=
      abs_sub _ _
    _ = _ := by rw [abs_of_pos (positiveProduct_pos j theta u hu true x),
      abs_of_pos (positiveProduct_pos j theta u hu false x)]

/-- The actual W has L1 norm at most one for EVERY coefficient vector
in the cube. This is not supplied as a duality hypothesis. -/
theorem integral_abs_testFunction_le_one {n : ℕ} (j : Fin (n+1)) (theta : ℝ)
    (u : Shell (n+1) h → ℝ) (hu : ∀ R, |u R| ≤ 1) :
    (∫ x, |testFunction j theta u x| ∂Haar.cubeMeasure (n+1)) ≤ 1 := by
  have hi := integral_mono (integrable_testFunction j theta u hu).abs
    (((integrable_positiveProduct j theta u hu true).add
      (integrable_positiveProduct j theta u hu false)).div_const 2)
    (abs_testFunction_le_products j theta u hu)
  simp only [Pi.add_apply] at hi
  rw [integral_div, integral_add (integrable_positiveProduct j theta u hu true)
    (integrable_positiveProduct j theta u hu false),
    integral_positiveProduct j theta u hu true,
    integral_positiveProduct j theta u hu false] at hi
  norm_num at hi ⊢
  exact hi

end Tusnady.Witness
