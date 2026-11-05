import Tusnady.FrameWhitening
import Tusnady.FrameLTNumerics

/-! Numerical and exact energy-coordinate transfer for the two-part frame
partition. These lemmas do not assert an unproved partition existence. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Frame
open Set
open scoped BigOperators InnerProductSpace
variable {D M : ℕ}

/-- The actual r=2 MSS upper factor for a tight frame. -/
def partitionFactor (ε : ℝ) : ℝ := (1+Real.sqrt (2*ε))^2/2

lemma partition_sqrt_le {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/100) :
    Real.sqrt ε ≤ 1/10 := by
  have hs := Real.sq_sqrt hε
  nlinarith [Real.sqrt_nonneg ε]

/-- The numerical enlargement in LT Proposition 2.1, with a universal
constant and the precise normalized smallness condition. -/
lemma partitionFactor_le {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/100) :
    partitionFactor ε ≤ (1+5*Real.sqrt ε)/2 := by
  have ht := partition_sqrt_le hε hsmall
  have hs := Real.sq_sqrt hε
  have hs2 := Real.sq_sqrt (show 0 ≤ 2*ε by positivity)
  have hh : Real.sqrt (2*ε) ≤ 2*Real.sqrt ε := by
    nlinarith [Real.sqrt_nonneg ε,Real.sqrt_nonneg (2*ε)]
  have he : ε ≤ Real.sqrt ε/10 := by
    nlinarith [Real.sqrt_nonneg ε]
  unfold partitionFactor
  nlinarith [Real.sqrt_nonneg ε]

lemma partition_lower_nonneg {ε : ℝ} (hε : 0 ≤ ε) (hsmall : ε ≤ 1/100) :
    0 ≤ (1-5*Real.sqrt ε)/2 := by
  have ht := partition_sqrt_le hε hsmall
  linarith

/-- Exact transport of both tight-frame partition estimates through a
proved whitening map. The hypotheses concern the actual two finite energies
and the actual energy-coordinate map; existence is supplied separately by
MSS and `exists_whitening`. -/
theorem partition_transfer (v u : Fin M → Space D) (α β δ : ℝ)
    (hδ : 0 < δ) (hα : 100*δ ≤ α) (hu : Tight u)
    (L : Space D →ₗ[ℝ] Space D)
    (hE : ∀ S x, energy v S x = energy u S (L x))
    (hL : ∀ x, α*‖x‖^2 ≤ ‖L x‖^2 ∧ ‖L x‖^2 ≤ β*‖x‖^2)
    (S : Finset (Fin M))
    (hS : ∀ y, energy u S y ≤ partitionFactor (δ/α)*‖y‖^2)
    (hcomp : ∀ y, energy u (Finset.univ \ S) y ≤ partitionFactor (δ/α)*‖y‖^2) :
    (∀ x, lowerStep δ α*‖x‖^2 ≤ energy v S x ∧
      energy v S x ≤ upperStep δ α β*‖x‖^2) ∧
    (∀ x, lowerStep δ α*‖x‖^2 ≤ energy v (Finset.univ \ S) x ∧
      energy v (Finset.univ \ S) x ≤ upperStep δ α β*‖x‖^2) := by
  classical
  have ha : 0 < α := lt_of_lt_of_le (by positivity) hα
  have he : 0 ≤ δ/α := div_nonneg hδ.le ha.le
  have hsmall : δ/α ≤ 1/100 := (div_le_iff₀ ha).2 (by linarith)
  let a : ℝ := (1-5*Real.sqrt (δ/α))/2
  let b : ℝ := (1+5*Real.sqrt (δ/α))/2
  have han : 0 ≤ a := partition_lower_nonneg he hsmall
  have hbn : 0 ≤ b := by dsimp only [b]; positivity
  have hfactor : partitionFactor (δ/α) ≤ b := partitionFactor_le he hsmall
  have hSu (y : Space D) : energy u S y ≤ b*‖y‖^2 :=
    (hS y).trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg _))
  have hCu (y : Space D) : energy u (Finset.univ \ S) y ≤ b*‖y‖^2 :=
    (hcomp y).trans (mul_le_mul_of_nonneg_right hfactor (sq_nonneg _))
  have hsum (y : Space D) : energy u S y+energy u (Finset.univ \ S) y = ‖y‖^2 := by
    rw [← hu y]
    unfold energy
    exact Finset.sum_add_sum_compl S _
  have hSl (y : Space D) : a*‖y‖^2 ≤ energy u S y := by
    have hh := hsum y
    have hc := hCu y
    dsimp only [a,b] at *
    nlinarith
  have hCl (y : Space D) : a*‖y‖^2 ≤ energy u (Finset.univ \ S) y := by
    have hh := hsum y
    have hc := hSu y
    dsimp only [a,b] at *
    nlinarith
  have htransfer (T : Finset (Fin M))
      (hTl : ∀ y, a*‖y‖^2 ≤ energy u T y) (hTu : ∀ y, energy u T y ≤ b*‖y‖^2)
      (x : Space D) : lowerStep δ α*‖x‖^2 ≤ energy v T x ∧
        energy v T x ≤ upperStep δ α β*‖x‖^2 := by
    rw [hE]
    constructor
    · calc
        _ = a*(α*‖x‖^2) := by dsimp only [a,lowerStep]; ring
        _ ≤ a*‖L x‖^2 := mul_le_mul_of_nonneg_left (hL x).1 han
        _ ≤ _ := hTl (L x)
    · calc
        _ ≤ b*‖L x‖^2 := hTu (L x)
        _ ≤ b*(β*‖x‖^2) := mul_le_mul_of_nonneg_left (hL x).2 hbn
        _ = _ := by dsimp only [b,upperStep]; ring
  exact ⟨htransfer S hSl hSu,htransfer _ hCl hCu⟩

end Tusnady.Frame
