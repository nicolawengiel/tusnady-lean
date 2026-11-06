import Tusnady.Upper.Ehrhard.GaussianRotation
import Tusnady.Upper.Ehrhard.GaussianBallAsymptotics
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# A closed convex set of Gaussian mass at least one half contains the origin

Strict separation from zero gives a strictly negative Gaussian halfspace.
Its probability is strictly below one half by the actual normalized marginal
law.  No symmetry assumption on the set is needed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace OAI.GaussianPropeller
open Quantile
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

theorem closedConvex_zero_mem_of_half_gaussianMass
    (K : Set E) (hKclosed : IsClosed K) (hKconvex : Convex ℝ K)
    (hKmass : (1 : ℝ)/2 ≤ (gaussianMeasure ι).real K) : (0 : E) ∈ K := by
  by_contra hz
  obtain ⟨f, a, hfa, ha⟩ := geometric_hahn_banach_closed_point hKconvex hKclosed hz
  have ha0 : a < 0 := by simpa using ha
  obtain ⟨x, hx⟩ := nonempty_of_measureReal_ne_zero
    (show (gaussianMeasure ι).real K ≠ 0 by linarith)
  let u : E := (InnerProductSpace.toDual ℝ E).symm f
  have huf (z : E) : inner ℝ u z = f z := InnerProductSpace.toDual_symm_apply
  have hu : u ≠ 0 := by
    intro hu0
    have hfx := hfa x hx
    rw [← huf x, hu0, inner_zero_left] at hfx
    linarith
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let v : E := (‖u‖)⁻¹ • u
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hn.ne']
  have hlaw : (gaussianMeasure ι).map (fun z => inner ℝ v z) = gaussianReal 0 1 := by
    simpa only [hv, one_pow, Real.toNNReal_one] using gaussianMeasure_inner_law v
  have hsub : K ⊆ {z | inner ℝ v z ≤ a/‖u‖} := by
    intro z hzK
    change inner ℝ v z ≤ a/‖u‖
    dsimp only [v]
    rw [real_inner_smul_left, huf, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hfa z hzK).le hn.le
  have hm : (gaussianMeasure ι).real {z | inner ℝ v z ≤ a/‖u‖} = Φ (a/‖u‖) := by
    rw [Φ_eq_gaussianReal, measureReal_def, measureReal_def, ← hlaw,
      Measure.map_apply (by fun_prop) measurableSet_Iic]
    rfl
  have hbelow : Φ (a/‖u‖) < (1 : ℝ)/2 := by
    rw [← Φ_zero]
    exact strictMono_Φ (div_neg_of_neg_of_pos ha0 hn)
  have hbound := (measureReal_mono hsub).trans_eq hm
  linarith

end OAI.GaussianPropeller
