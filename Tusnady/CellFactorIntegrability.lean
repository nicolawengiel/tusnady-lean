import Tusnady.CellFactors

/-! # Concrete square-integrability and exact retained-component norms. -/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.DyadicFunctions Tusnady.Haar
open scoped BigOperators

lemma tentI_continuous (a : ℕ) (i : Fin (2^a)) : Continuous (tentI a i) := by
  have h := (hI_integrable a i).continuous_primitive (1:ℝ)
  have heq : tentI a i = (fun p => ∫ x in (1:ℝ)..p, hI a i x) := by
    funext p
    have hp := integral_hI_right_unit a i p
    rw [intervalIntegral.integral_symm] at hp
    linarith
  rw [heq]
  exact h

@[fun_prop]
theorem factorPrimitive_continuous {H : ℕ} (f : Factor H) : Continuous (factorPrimitive f) := by
  cases f with
  | constant c => exact continuous_const.mul (continuous_const.sub continuous_id)
  | haar a i c => exact continuous_const.mul (tentI_continuous a.val i).neg
  | walsh a ha i c => exact continuous_const.mul (psiI_continuous a i)

@[fun_prop]
theorem tensorFactorPrimitive_continuous {d H : ℕ} (f : Fin d → Factor H) :
    Continuous (tensorFactorPrimitive f) := by
  unfold tensorFactorPrimitive
  apply continuous_finset_prod
  intro k _
  exact (factorPrimitive_continuous (f k)).comp (continuous_apply k)

lemma factorPrimitiveMass_pos_or_zero {H : ℕ} (f : Factor H) :
    0 < factorPrimitiveMass f ∨ ∀ p, factorPrimitive f p = 0 := by
  cases f with
  | constant c =>
    by_cases hc : c = 0
    · right
      intro p
      simp [factorPrimitive, hc]
    · left
      have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
      unfold factorPrimitiveMass
      positivity
  | haar a i c =>
    by_cases hc : c = 0
    · right
      intro p
      simp [factorPrimitive, hc]
    · left
      have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
      have hl := dyadicLength_pos a.val
      unfold factorPrimitiveMass
      positivity
  | walsh a ha i c =>
    by_cases hc : c = 0
    · right
      intro p
      simp [factorPrimitive, hc]
    · left
      have hc2 : 0 < c^2 := sq_pos_of_ne_zero hc
      have hl := dyadicLength_pos a
      unfold factorPrimitiveMass
      positivity

/-- The concrete mixed tensor primitive is genuinely in L², including all
zero-coefficient cases. The nonzero case uses the proved exact positive
integral, so no integrability premise is hidden in the norm identity. -/
theorem tensorFactorPrimitive_memLp {d H : ℕ} (f : Fin d → Factor H) :
    MemLp (tensorFactorPrimitive f) 2 (cubeMeasure d) := by
  classical
  by_cases hpos : ∀ k, 0 < factorPrimitiveMass (f k)
  · have hm : 0 < ∏ k, factorPrimitiveMass (f k) := Finset.prod_pos (fun k _ => hpos k)
    have hint : Integrable (fun p => tensorFactorPrimitive f p^2) (cubeMeasure d) := by
      by_contra h
      have heq := integral_tensorFactorPrimitive_sq f
      rw [integral_undef h] at heq
      linarith
    exact (memLp_two_iff_integrable_sq
      (tensorFactorPrimitive_continuous f).measurable.aestronglyMeasurable).2 hint
  · have hex : ∃ k, ¬ 0 < factorPrimitiveMass (f k) := by simpa only [not_forall] using hpos
    obtain ⟨k,hk⟩ := hex
    rcases factorPrimitiveMass_pos_or_zero (f k) with hp | hzero
    · exact False.elim (hk hp)
    · have hfun : tensorFactorPrimitive f = (fun _ => (0:ℝ)) := by
        funext p
        exact Finset.prod_eq_zero (Finset.mem_univ k) (hzero (p k))
      rw [hfun]
      exact MemLp.zero

/-- Exact L² norm identity for the actual high-projected component. -/
theorem integral_boxPrimitive_high_tensorFactor_sq {d H : ℕ} (h : ℕ) (f : Fin d → Factor H) :
    (∫ p, Tusnady.boxPrimitive (highProjection d H h (tensorFactorL2 f)) p^2 ∂cubeMeasure d) =
      if (h:ℤ) ≤ tensorFactorLevel f then ∏ k, factorPrimitiveMass (f k) else 0 := by
  have hae : (fun p => Tusnady.boxPrimitive (highProjection d H h (tensorFactorL2 f)) p^2) =ᵐ[cubeMeasure d]
      (fun p => (if (h:ℤ) ≤ tensorFactorLevel f then tensorFactorPrimitive f p else 0)^2) := by
    filter_upwards [cubeMeasure_ae_UnitCube d] with p hp
    rw [boxPrimitive_high_tensorFactor h f p hp]
  rw [integral_congr_ae hae]
  by_cases hl : (h:ℤ) ≤ tensorFactorLevel f
  · simp only [if_pos hl]
    exact integral_tensorFactorPrimitive_sq f
  · simp [hl]

/-- The actual primitive of the high-projected component is in L². -/
theorem boxPrimitive_high_tensorFactor_memLp {d H : ℕ} (h : ℕ) (f : Fin d → Factor H) :
    MemLp (fun p => Tusnady.boxPrimitive (highProjection d H h (tensorFactorL2 f)) p)
      2 (cubeMeasure d) := by
  have hae : (fun p => Tusnady.boxPrimitive (highProjection d H h (tensorFactorL2 f)) p) =ᵐ[cubeMeasure d]
      (fun p => if (h:ℤ) ≤ tensorFactorLevel f then tensorFactorPrimitive f p else 0) := by
    filter_upwards [cubeMeasure_ae_UnitCube d] with p hp
    exact boxPrimitive_high_tensorFactor h f p hp
  apply (memLp_congr_ae hae).2
  by_cases hl : (h:ℤ) ≤ tensorFactorLevel f
  · simp only [if_pos hl]
    exact tensorFactorPrimitive_memLp f
  · simp only [if_neg hl]
    exact MemLp.zero

end Tusnady.Cell
