import Tusnady.CellReindex

/-!
# Continuity of the actual projected cubic cell primitives

The physical high primitive equals a finite sum of products of actual
continuous affine, Haar-tent, and Walsh-primitive factors on the unit cube.
No continuity assumption on a representative of an L² class is introduced.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.Dyadic Tusnady.DyadicFunctions Tusnady.Haar Tusnady.Witness
open scoped BigOperators
variable {d h H : ℕ}

lemma continuousOn_boxPrimitive_high_cell (h : ℕ) (j : Fin d → ℕ)
    (hj : ∀ k, j k+2 < H) (I : CellIndices j) (m : Fin d → Bool) :
    ContinuousOn (fun p => Tusnady.boxPrimitive (highProjection d H h (cellL2 j hj I m)) p)
      (Tusnady.UnitCube d) := by
  have hs : Continuous (fun p => ∑ b ∈ retainedComponents h j hj I m,
      tensorFactorPrimitive (cellComponentFactors j hj I m b) p) :=
    continuous_finset_sum _ (fun b _ => tensorFactorPrimitive_continuous _)
  apply hs.continuousOn.congr
  intro p hp
  exact boxPrimitive_high_cell_eq_sum h j hj I m p hp

/-- Continuity on the actual unit cube for every physical nonempty
shell family, including incompatible choices (whose projection is zero). -/
theorem continuousOn_boxPrimitive_high_family (S : Finset (Shape d h)) (hS : S.Nonempty)
    (hj : ∀ k, join S k+2 < H) (c : Family S) :
    ContinuousOn (fun p => Tusnady.boxPrimitive (highProjection d H h (familyL2 S hS hj c)) p)
      (Tusnady.UnitCube d) := by
  classical
  by_cases hc : Compatible S c
  · obtain ⟨I,rfl⟩ := compatible_mem_range S hS c hc
    rw [familyL2_ancestor,highProjection_smul]
    apply (continuousOn_const.mul (continuousOn_boxPrimitive_high_cell h (join S) hj I (peakModulated S))).congr
    intro p hp
    exact boxPrimitive_L2_smul (cellSign S I) _ p hp
  · have hv : familyL2 S hS hj c = 0 := by simp [familyL2,hc]
    have hz : highProjection d H h (0 : Lp ℝ 2 (cubeMeasure d)) = 0 := by
      unfold highProjection lowProjection projectionFor
      simp
    rw [hv,hz]
    apply (continuousOn_const : ContinuousOn (fun _ : Tusnady.Point d => (0:ℝ)) (Tusnady.UnitCube d)).congr
    intro p hp
    exact boxPrimitive_L2_zero p hp

end Tusnady.Cell

namespace Tusnady.Witness
open MeasureTheory Set
open scoped BigOperators
variable {d h H : ℕ} {j : Fin d}

/-- Actual W cell-vector primitive continuity, via its proved physical
family representation. -/
theorem continuousOn_boxPrimitive_high_cellL2Vector (S : Finset (BlockShape j h))
    (hS : S.Nonempty) (H : ℕ) (hj : ∀ k, Dyadic.join (physicalShapes S) k+2 < H)
    (c : CellChoice S) :
    ContinuousOn (fun p => boxPrimitive (Haar.highProjection d H h (cellL2Vector ⟨S,c⟩)) p) (UnitCube d) := by
  rw [cellL2Vector_eq_familyL2 S hS H hj c]
  exact Cell.continuousOn_boxPrimitive_high_family (physicalShapes S) (physicalShapes_nonempty S hS) hj _

/-- Zero coefficients are handled explicitly, so the full finite cubic
energy density is continuous even when its cell family is empty. -/
theorem continuousOn_cubic_weighted_primitive (hd : 0 < d) (theta : ℝ) (G : CellIndex j h) :
    ContinuousOn (fun p => cubicCoefficient j theta G *
      boxPrimitive (Haar.highProjection d (h+3*d) h (cellL2Vector G)) p) (UnitCube d) := by
  by_cases hc : cubicCoefficient j theta G = 0
  · simp only [hc,zero_mul]
    exact continuousOn_const
  · have hs : shapeCoefficient j theta G.1 ≠ 0 := by
      intro hs
      exact hc (by simp [cubicCoefficient,hs])
    have hne := shapeCoefficient_nonempty theta G.1 hs
    exact continuousOn_const.mul (continuousOn_boxPrimitive_high_cellL2Vector G.1 hne
      (h+3*d) (Cell.join_cap _ hd) G.2)

/-- The actual nonnegative cubic energy density from Main.pdf (4.7). -/
def cubicEnergyDensity (j : Fin d) (theta : ℝ) (p : Point d) : ℝ :=
  ∑ G : CellIndex j h, cubicCoefficient j theta G^2*(1/3:ℝ)^(variableSet G).card*
    boxPrimitive (Haar.highProjection d (h+3*d) h (cellL2Vector G)) p^2

theorem cubicEnergyDensity_nonneg (j : Fin d) (theta : ℝ) (p : Point d) :
    0 ≤ cubicEnergyDensity (h := h) j theta p := by
  unfold cubicEnergyDensity
  apply Finset.sum_nonneg
  intro G _
  positivity

theorem cubicEnergyDensity_continuousOn (hd : 0 < d) (j : Fin d) (theta : ℝ) :
    ContinuousOn (cubicEnergyDensity (h := h) j theta) (UnitCube d) := by
  have heq : cubicEnergyDensity (h := h) j theta = fun p =>
      ∑ G : CellIndex j h, (1/3:ℝ)^(variableSet G).card*
        (cubicCoefficient j theta G *
          boxPrimitive (Haar.highProjection d (h+3*d) h (cellL2Vector G)) p)^2 := by
    funext p
    apply Finset.sum_congr rfl
    intro G _
    ring
  rw [heq]
  apply continuousOn_finset_sum
  intro G _
  exact continuousOn_const.mul ((continuousOn_cubic_weighted_primitive hd theta G).pow 2)

end Tusnady.Witness
