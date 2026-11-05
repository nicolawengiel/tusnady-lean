import Tusnady.CellCoordinateProduct

/-!
# Actual shell-family products in L² and the fixed-shape cell estimate

The vector used here is tied by an almost-everywhere theorem to the actual
product of the selected shell functions. Compatible families are identified
with their unique actual join cells; incompatible families have zero product.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.Dyadic Tusnady.DyadicFunctions Tusnady.Haar Tusnady.Witness
open scoped BigOperators
variable {d h H : ℕ}

def familyL2 (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) (c : Family S) : Lp ℝ 2 (cubeMeasure d) := by
  classical
  exact if hc : Compatible S c then
    let I := (familyCellEquiv S hS).symm ⟨c,hc⟩
    cellSign S I • cellL2 (join S) hj I (peakModulated S)
  else 0

lemma familyL2_ancestor (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) (I : CellIndices (join S)) :
    familyL2 S hS hj (boxFamilyFromCell S I) =
      cellSign S I • cellL2 (join S) hj I (peakModulated S) := by
  classical
  unfold familyL2
  rw [dif_pos (ancestorFamily_compatible S I)]
  have hi : (familyCellEquiv S hS).symm
      ⟨boxFamilyFromCell S I,ancestorFamily_compatible S I⟩ = I :=
    (familyCellEquiv S hS).symm_apply_apply I
  simp only [hi]

/-- The constructed L² vector represents the actual shell product. -/
theorem familyL2_ae (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) (c : Family S) :
    familyL2 S hS hj c =ᵐ[cubeMeasure d] familyProduct S c := by
  classical
  by_cases hc : Compatible S c
  · obtain ⟨I,rfl⟩ := compatible_mem_range S hS c hc
    rw [familyL2_ancestor]
    filter_upwards [Lp.coeFn_smul (cellSign S I) (cellL2 (join S) hj I (peakModulated S)),
      cellL2_ae (join S) hj I (peakModulated S)] with x hs hcell
    simpa only [Pi.smul_apply, smul_eq_mul, hcell, familyProduct_factorization S hS I x] using hs
  · have hz : ∀ x, familyProduct S c x = 0 := by
      intro x
      by_contra hx
      exact hc ((compatible_iff_product_nonzero S c).2 ⟨x,hx⟩)
    unfold familyL2
    rw [dif_neg hc]
    filter_upwards [Lp.coeFn_zero ℝ 2 (cubeMeasure d)] with x hx
    simpa only [hz, Pi.zero_apply] using hx

lemma highProjection_smul (c : ℝ) (f : Lp ℝ 2 (cubeMeasure d)) :
    highProjection d H h (c • f) = c • highProjection d H h f := by
  unfold highProjection lowProjection projectionFor
  simp only [map_smul, Submodule.coe_smul, smul_sub]

lemma boxPrimitive_L2_smul (c : ℝ) (f : Lp ℝ 2 (cubeMeasure d))
    (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive (c • f : Lp ℝ 2 (cubeMeasure d)) p = c*Tusnady.boxPrimitive f p := by
  rw [boxPrimitive_congr_cube_ae _ _ (Lp.coeFn_smul c f) p hp]
  exact Tusnady.boxPrimitive_const_mul c f p

lemma boxPrimitive_L2_zero (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive (0 : Lp ℝ 2 (cubeMeasure d)) p = 0 := by
  rw [boxPrimitive_congr_cube_ae _ _ (Lp.coeFn_zero ℝ 2 (cubeMeasure d)) p hp]
  simp [Tusnady.boxPrimitive]

def familyEnergy (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) (c : Family S) : ℝ :=
  ∫ p, Tusnady.boxPrimitive (highProjection d H h (familyL2 S hS hj c)) p^2 ∂cubeMeasure d

theorem familyEnergy_ancestor (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) (I : CellIndices (join S)) :
    familyEnergy S hS hj (boxFamilyFromCell S I) =
      ∫ p, Tusnady.boxPrimitive (highProjection d H h
        (cellL2 (join S) hj I (peakModulated S))) p^2 ∂cubeMeasure d := by
  unfold familyEnergy
  rw [familyL2_ancestor, highProjection_smul]
  apply integral_congr_ae
  filter_upwards [cubeMeasure_ae_UnitCube d] with p hp
  rw [boxPrimitive_L2_smul _ _ p hp, mul_pow]
  have hs : cellSign S I^2 = 1 := by rw [← sq_abs, cellSign_abs]; norm_num
  rw [hs, one_mul]

lemma familyEnergy_zero (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) (c : Family S) (hc : ¬ Compatible S c) :
    familyEnergy S hS hj c = 0 := by
  unfold familyEnergy familyL2
  rw [dif_neg hc]
  have hz : highProjection d H h (0 : Lp ℝ 2 (cubeMeasure d)) = 0 := by
    unfold highProjection lowProjection projectionFor
    simp
  rw [hz]
  calc
    _ = ∫ _p, (0:ℝ) ∂cubeMeasure d := by
      apply integral_congr_ae
      filter_upwards [cubeMeasure_ae_UnitCube d] with p hp
      rw [boxPrimitive_L2_zero p hp]
      norm_num
    _ = 0 := integral_zero _ _

end Tusnady.Cell

namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.Dyadic Tusnady.DyadicFunctions Tusnady.Haar Tusnady.Witness
open scoped BigOperators
variable {d h H : ℕ}

/-- Summing actual shell-family energies is exactly summing cell energies;
incompatible choices contribute zero and compatible choices occur once. -/
theorem sum_familyEnergy_eq_cells (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) :
    (∑ c : Family S, familyEnergy S hS hj c) =
      ∑ I : CellIndices (join S), ∫ p, Tusnady.boxPrimitive
        (highProjection d H h (cellL2 (join S) hj I (peakModulated S))) p^2 ∂cubeMeasure d := by
  classical
  calc
    _ = ∑ c ∈ (Finset.univ.filter (Compatible S)), familyEnergy S hS hj c := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro c _ hnot
      apply familyEnergy_zero S hS hj c
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
    _ = ∑ c : {c : Family S // Compatible S c}, familyEnergy S hS hj c.val :=
      Finset.sum_subtype _ (by simp) _
    _ = ∑ I : CellIndices (join S), familyEnergy S hS hj (boxFamilyFromCell S I) :=
      ((familyCellEquiv S hS).sum_comp (fun c => familyEnergy S hS hj c.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro I _
      exact familyEnergy_ancestor S hS hj I

/-- The full fixed-shape family version of Manuscript Lemma 4.3, with the
actual qShell products and the actual orthogonal high projection. -/
theorem family_cell_location (S : Finset (Shape d h)) (hS : S.Nonempty) (hd : 0 < d)
    (hj : ∀ k, join S k+2 < H) (hmod : peakModulated S ⟨0,hd⟩ = true) :
    (∑ c : Family S, familyEnergy S hS hj c) ≤
      cellLocationConstant d*dyadicLength h^2*dyadicLength (excess S)*
        ((excess S+1:ℕ):ℝ)^(2*(d-1)) := by
  rw [sum_familyEnergy_eq_cells S hS hj]
  apply cell_location d H h (excess S) hd (join S) hj (peakModulated S)
  · exact (excess_add_shell S hS).symm.trans (Nat.add_comm _ _)
  · exact hmod

/-- A convenient cap suffices for every shell shape; no cap hypothesis
needs to be carried by the final application. -/
lemma join_cap (S : Finset (Shape d h)) (hd : 0 < d) (k : Fin d) : join S k+2 < h+3*d := by
  have hk := join_le_shell S k
  omega

end Tusnady.Cell
