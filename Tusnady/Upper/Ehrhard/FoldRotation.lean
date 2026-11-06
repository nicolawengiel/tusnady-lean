import Tusnady.Upper.Ehrhard.GaussianRotation
import Tusnady.Upper.Ehrhard.GaussianSections
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Orthogonal reduction of the concrete fold to the last coordinate

Equivariance is proved for the actual algebraic fold.  A reflection then maps
any vector to its norm times the last coordinate direction.  The measure
comparison uses proved orthogonal invariance of the actual Gaussian measure.
-/
noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace
namespace OAI.GaussianPropeller
open Tusnady.Upper GaussianSections

theorem image_signingFold {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (e : E ≃ₗ[ℝ] F) (K : Set E) (u : E) :
    e '' signingFold u K = signingFold (e u) (e '' K) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, t, hm, hp, ht, rfl⟩ := (mem_signingFold_iff K u x).mp hx
    apply (mem_signingFold_iff (e '' K) (e u) _).mpr
    refine ⟨e c, t, ?_, ?_, ht, ?_⟩
    · exact ⟨c-u, hm, e.map_sub c u⟩
    · exact ⟨c+u, hp, e.map_add c u⟩
    · simp
  · intro hz
    obtain ⟨c, t, hm, hp, ht, heq⟩ := (mem_signingFold_iff (e '' K) (e u) z).mp hz
    obtain ⟨a, ha, hea⟩ := hm
    obtain ⟨b, hb, heb⟩ := hp
    have ha' : e.symm c-u ∈ K := by
      have he : a = e.symm c-u := e.injective (by simpa only [map_sub, e.apply_symm_apply] using hea)
      exact he ▸ ha
    have hb' : e.symm c+u ∈ K := by
      have he : b = e.symm c+u := e.injective (by simpa only [map_add, e.apply_symm_apply] using heb)
      exact he ▸ hb
    refine ⟨e.symm c+t • u, (mem_signingFold_iff K u _).mpr
      ⟨e.symm c, t, ha', hb', ht, rfl⟩, ?_⟩
    simpa only [map_add, map_smul, e.apply_symm_apply] using heq.symm

theorem gaussianMeasure_real_image_isometry {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ)
    (K : Set (EuclideanSpace ℝ ι)) (hK : IsCompact K) :
    (gaussianMeasure κ).real (e '' K) = (gaussianMeasure ι).real K := by
  rw [measureReal_def, measureReal_def, ← gaussianMeasure_map_linearIsometryEquiv e,
    Measure.map_apply e.continuous.measurable (hK.image e.continuous).measurableSet]
  have heq : e ⁻¹' (e '' K) = K := by
    ext z
    simp only [mem_preimage, mem_image, e.injective.eq_iff, exists_eq_right]
  rw [heq]

theorem norm_axis {k : ℕ} (r : ℝ) : ‖axis (k := k) r‖ = |r| := by
  have hsq : ‖axis (k := k) r‖^2 = r^2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_castSucc]
    simp [axis, append, Real.norm_eq_abs, sq_abs]
  nlinarith [norm_nonneg (axis (k := k) r), abs_nonneg r, sq_abs r]

theorem exists_isometry_to_axis {k : ℕ} (u : EuclideanSpace ℝ (Fin (k+1))) :
    ∃ e : EuclideanSpace ℝ (Fin (k+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (k+1)),
      e u = axis ‖u‖ := by
  have hn : ‖u‖ = ‖axis (k := k) ‖u‖‖ := by rw [norm_axis, abs_of_nonneg (norm_nonneg u)]
  exact ⟨(ℝ ∙ (u-axis ‖u‖))ᗮ.reflection, Submodule.reflection_sub hn⟩

end OAI.GaussianPropeller
