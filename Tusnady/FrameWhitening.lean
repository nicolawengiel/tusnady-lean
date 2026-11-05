import Tusnady.FrameBasic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Actual frame whitening from the analysis-map range. No square root,
spectral diagonalization or change-of-inner-product assertion is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Frame
open Set
open scoped BigOperators InnerProductSpace
variable {D M : ℕ}

/-- The genuine finite-frame analysis map. -/
def analysis (v : Fin M → Space D) : Space D →ₗ[ℝ] Space M where
  toFun x := WithLp.toLp 2 (fun j => inner ℝ x (v j))
  map_add' x y := by ext j; simp [inner_add_left]
  map_smul' c x := by ext j; simp [inner_smul_left]

@[simp] lemma analysis_apply (v : Fin M → Space D) (x : Space D) (j : Fin M) :
    analysis v x j = inner ℝ x (v j) := rfl

lemma analysis_norm_sq (v : Fin M → Space D) (x : Space D) :
    ‖analysis v x‖^2 = energy v Finset.univ x := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [energy,Real.norm_eq_abs]

lemma analysis_injective_of_lower (v : Fin M → Space D) (α : ℝ) (hα : 0 < α)
    (hlower : ∀ x, α*‖x‖^2 ≤ energy v Finset.univ x) : Function.Injective (analysis v) := by
  have hz : ∀ x, analysis v x = 0 → x = 0 := by
    intro x hx
    have hh := hlower x
    rw [← analysis_norm_sq,hx,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hh
    have he : α*‖x‖^2 = 0 := le_antisymm hh (mul_nonneg hα.le (sq_nonneg _))
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp he).resolve_left hα.ne'))
  intro x y hxy
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,hxy,sub_self]

/-- The range of the actual analysis map is canonically isometric to
Euclidean dimension D after choosing an orthonormal basis. Its composition
with analysis is a genuine linear equivalence whose squared norm is the
original frame energy. -/
theorem exists_energy_equiv (v : Fin M → Space D) (α : ℝ) (hα : 0 < α)
    (hlower : ∀ x, α*‖x‖^2 ≤ energy v Finset.univ x) :
    ∃ L : Space D ≃ₗ[ℝ] Space D, ∀ x, ‖L x‖^2 = energy v Finset.univ x := by
  let T := analysis v
  have hinj : Function.Injective T := analysis_injective_of_lower v α hα hlower
  have hdim : Module.finrank ℝ (LinearMap.range T) = D := by
    rw [LinearMap.finrank_range_of_inj hinj]
    exact finrank_euclideanSpace_fin
  let b : OrthonormalBasis (Fin D) ℝ (LinearMap.range T) :=
    (stdOrthonormalBasis ℝ (LinearMap.range T)).reindex (finCongr hdim)
  let L : Space D ≃ₗ[ℝ] Space D := (LinearEquiv.ofInjective T hinj).trans b.repr.toLinearEquiv
  refine ⟨L,fun x => ?_⟩
  change ‖b.repr (LinearEquiv.ofInjective T hinj x)‖^2 = _
  rw [b.repr.norm_map]
  exact analysis_norm_sq v x

/-- Actual whitening with an invertible energy-coordinate map. The
individual norm bound is proved from Cauchy--Schwarz and the given lower
energy bound; it is not an additional operator-norm premise. -/
theorem exists_whitening_equiv (v : Fin M → Space D) (α β δ : ℝ) (hα : 0 < α)
    (hlower : ∀ x, α*‖x‖^2 ≤ energy v Finset.univ x)
    (hupper : ∀ x, energy v Finset.univ x ≤ β*‖x‖^2)
    (hv : ∀ j, ‖v j‖^2 ≤ δ) :
    ∃ u : Fin M → Space D, Tight u ∧ (∀ j, ‖u j‖^2 ≤ δ/α) ∧
      ∃ L : Space D ≃ₗ[ℝ] Space D,
        (∀ S x, energy v S x = energy u S (L x)) ∧
        (∀ x, α*‖x‖^2 ≤ ‖L x‖^2 ∧ ‖L x‖^2 ≤ β*‖x‖^2) := by
  obtain ⟨L,hL⟩ := exists_energy_equiv v α hα hlower
  let A : Space D →L[ℝ] Space D := L.symm.toLinearMap.toContinuousLinearMap
  let u : Fin M → Space D := fun j => A.adjoint (v j)
  have hinner (x : Space D) (j : Fin M) : inner ℝ x (u j) = inner ℝ (L.symm x) (v j) := by
    exact A.adjoint_inner_right x (v j)
  have henergy (S : Finset (Fin M)) (x : Space D) : energy u S x = energy v S (L.symm x) := by
    simp only [energy,hinner]
  have hTight : Tight u := by
    intro x
    rw [henergy,← hL,L.apply_symm_apply]
  have hunorm (j : Fin M) : ‖u j‖^2 ≤ δ/α := by
    have hδ : 0 ≤ δ := (sq_nonneg _).trans (hv j)
    by_cases hu0 : ‖u j‖^2 = 0
    · rw [hu0]
      exact div_nonneg hδ hα.le
    have hup : 0 < ‖u j‖^2 := lt_of_le_of_ne (sq_nonneg _) (by intro he; exact hu0 he.symm)
    have hlow : α*‖L.symm (u j)‖^2 ≤ ‖u j‖^2 := by
      have hh := hlower (L.symm (u j))
      rwa [← hL,L.apply_symm_apply] at hh
    have hcs := real_inner_mul_inner_self_le (L.symm (u j)) (v j)
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hcs
    have hid : inner ℝ (L.symm (u j)) (v j) = ‖u j‖^2 := by
      rw [← hinner,real_inner_self_eq_norm_sq]
    rw [hid] at hcs
    have hprod : α*(‖u j‖^2*‖u j‖^2) ≤ ‖u j‖^2*δ := by
      calc
        _ ≤ α*(‖L.symm (u j)‖^2*‖v j‖^2) := mul_le_mul_of_nonneg_left hcs hα.le
        _ = (α*‖L.symm (u j)‖^2)*‖v j‖^2 := by ring
        _ ≤ ‖u j‖^2*δ := mul_le_mul hlow (hv j) (sq_nonneg _) (sq_nonneg _)
    have hcancel : α*‖u j‖^2 ≤ δ := (mul_le_mul_iff_left₀ hup).mp (by nlinarith only [hprod])
    exact (le_div_iff₀ hα).2 (by nlinarith only [hcancel])
  refine ⟨u,hTight,hunorm,L,?_,?_⟩
  · intro S x
    rw [henergy,L.symm_apply_apply]
  · intro x
    rw [hL]
    exact ⟨hlower x,hupper x⟩

/-- The linear-map interface required for transporting a partition of the
whitened tight frame back to the original frame. -/
theorem exists_whitening (v : Fin M → Space D) (α β δ : ℝ) (hα : 0 < α)
    (hlower : ∀ x, α*‖x‖^2 ≤ energy v Finset.univ x)
    (hupper : ∀ x, energy v Finset.univ x ≤ β*‖x‖^2)
    (hv : ∀ j, ‖v j‖^2 ≤ δ) :
    ∃ u : Fin M → Space D, Tight u ∧ (∀ j, ‖u j‖^2 ≤ δ/α) ∧
      ∃ L : Space D →ₗ[ℝ] Space D,
        (∀ S x, energy v S x = energy u S (L x)) ∧
        (∀ x, α*‖x‖^2 ≤ ‖L x‖^2 ∧ ‖L x‖^2 ≤ β*‖x‖^2) := by
  obtain ⟨u,hu,hun,L,hE,hB⟩ := exists_whitening_equiv v α β δ hα hlower hupper hv
  exact ⟨u,hu,hun,L.toLinearMap,hE,hB⟩

end Tusnady.Frame
