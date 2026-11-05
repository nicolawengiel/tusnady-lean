import Tusnady.FiniteBlockPolynomial
import Tusnady.WalshOddExtension

/-!
# Actual coefficients of the block product polynomial

The finite expansion is an equality of concrete real functions. Its
coefficients are explicit products of the manuscript's Walsh coefficients.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Witness

abbrev BlockShape (j : Fin d) (h : ℕ) := (a : BlockIndex h) × ShapesInBlock j a

def blockPolynomialCoefficient (j : Fin d) (a : BlockIndex h) (theta c : ℝ)
    (T : Finset (ShapesInBlock j a)) : ℝ :=
  if T = ∅ then 1 else c * Walsh.coefficient (Walsh.smoothedBlock theta) T

lemma smoothedBlock_emptyCoefficient (theta : ℝ) {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Walsh.coefficient (Walsh.smoothedBlock theta : Walsh.Cube ι → ℝ) ∅ = 0 :=
  Walsh.smoothedBlock_even_coefficient theta ∅ (by simp)

/-- Exact constant-plus-block expansion, valid at all real arguments. -/
lemma blockPolynomial_expansion (j : Fin d) (a : BlockIndex h) (theta c : ℝ)
    (y : ShapesInBlock j a → ℝ) :
    1+c*Walsh.extension (Walsh.smoothedBlock theta) y =
      ∑ T : Finset (ShapesInBlock j a),
        blockPolynomialCoefficient j a theta c T * ∏ r ∈ T, y r := by
  classical
  have hterm (T : Finset (ShapesInBlock j a)) :
      blockPolynomialCoefficient j a theta c T * (∏ r ∈ T, y r) =
        (if T = ∅ then (1:ℝ) else 0) +
          c * (Walsh.coefficient (Walsh.smoothedBlock theta) T * ∏ r ∈ T, y r) := by
    by_cases hT : T = ∅
    · subst T
      simp [blockPolynomialCoefficient, smoothedBlock_emptyCoefficient]
    · simp only [blockPolynomialCoefficient, if_neg hT]
      ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl

def positiveShapeProduct (j : Fin d) (theta c : ℝ) (y : BlockShape j h → ℝ) : ℝ :=
  ∏ a : BlockIndex h, (1+c*Walsh.extension (Walsh.smoothedBlock theta)
    (fun r : ShapesInBlock j a => y ⟨a,r⟩))

def positiveShapeCoefficient (j : Fin d) (theta c : ℝ)
    (S : Finset (BlockShape j h)) : ℝ :=
  ∏ a : BlockIndex h, blockPolynomialCoefficient j a theta c (FiniteBlocks.fiber S a)

lemma positiveShapeProduct_expansion (j : Fin d) (theta c : ℝ)
    (y : BlockShape j h → ℝ) :
    positiveShapeProduct j theta c y =
      ∑ S : Finset (BlockShape j h), positiveShapeCoefficient j theta c S * ∏ r ∈ S, y r := by
  classical
  unfold positiveShapeProduct
  simp_rw [blockPolynomial_expansion]
  exact FiniteBlocks.product_expansion _ _

def shapeTest (j : Fin d) (theta : ℝ) (y : BlockShape j h → ℝ) : ℝ :=
  (positiveShapeProduct j theta (1/4) y-positiveShapeProduct j theta (-1/4) y)/2

def shapeCoefficient (j : Fin d) (theta : ℝ) (S : Finset (BlockShape j h)) : ℝ :=
  (positiveShapeCoefficient j theta (1/4) S-positiveShapeCoefficient j theta (-1/4) S)/2

theorem shapeTest_expansion (j : Fin d) (theta : ℝ) (y : BlockShape j h → ℝ) :
    shapeTest j theta y = ∑ S : Finset (BlockShape j h),
      shapeCoefficient j theta S * ∏ r ∈ S, y r := by
  classical
  unfold shapeTest shapeCoefficient
  rw [positiveShapeProduct_expansion, positiveShapeProduct_expansion,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- This is the expansion of the actual W defined in TestFunction.lean. -/
theorem testFunction_shapeExpansion (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) :
    testFunction j theta u x = ∑ S : Finset (BlockShape j h),
      shapeCoefficient j theta S * ∏ r ∈ S, layer r.2.val u x := by
  exact shapeTest_expansion j theta (fun r : BlockShape j h => layer r.2.val u x)

lemma positiveShapeProduct_neg (j : Fin d) (theta c : ℝ)
    (y : BlockShape j h → ℝ) :
    positiveShapeProduct j theta c (fun r => -y r) =
      positiveShapeProduct j theta (-c) y := by
  unfold positiveShapeProduct
  apply Finset.prod_congr rfl
  intro a _
  rw [Walsh.extension_neg_of_odd (Walsh.smoothedBlock_odd theta)]
  ring

lemma shapeTest_neg (j : Fin d) (theta : ℝ) (y : BlockShape j h → ℝ) :
    shapeTest j theta (fun r => -y r) = -shapeTest j theta y := by
  unfold shapeTest
  rw [positiveShapeProduct_neg, positiveShapeProduct_neg]
  norm_num
  ring

def shapeCubeFunction (j : Fin d) (theta : ℝ) (x : Walsh.Cube (BlockShape j h)) : ℝ :=
  shapeTest j theta (fun r => Walsh.bitSign (x r))

lemma shapeCubeFunction_odd (j : Fin d) (theta : ℝ)
    (x : Walsh.Cube (BlockShape j h)) :
    shapeCubeFunction j theta (Walsh.negateCube x) = -shapeCubeFunction j theta x := by
  unfold shapeCubeFunction
  simp only [Walsh.negateCube, Equiv.coe_fn_mk, Walsh.bitSign_not]
  exact shapeTest_neg j theta _

/-- The explicit product coefficient is exactly the Fourier coefficient
of the actual sign-cube function, not an arbitrary polynomial parameter. -/
theorem shapeCoefficient_eq_walsh (j : Fin d) (theta : ℝ)
    (S : Finset (BlockShape j h)) :
    shapeCoefficient j theta S = Walsh.coefficient (shapeCubeFunction j theta) S := by
  have heq : Walsh.synthesis (shapeCoefficient (h := h) j theta) =
      shapeCubeFunction (h := h) j theta := by
    funext x
    exact (shapeTest_expansion j theta (fun r => Walsh.bitSign (x r))).symm
  rw [← heq, Walsh.coefficient_synthesis]

theorem shapeCoefficient_even_eq_zero (j : Fin d) (theta : ℝ)
    (S : Finset (BlockShape j h)) (hS : Even S.card) :
    shapeCoefficient j theta S = 0 := by
  rw [shapeCoefficient_eq_walsh]
  exact Walsh.coefficient_even_eq_zero (shapeCubeFunction_odd j theta) S hS

lemma positiveShapeCoefficient_singleton (j : Fin d) (theta c : ℝ)
    (a : BlockIndex h) (r : ShapesInBlock j a) :
    positiveShapeCoefficient j theta c {⟨a,r⟩} =
      c*Walsh.coefficient (Walsh.smoothedBlock theta) {r} := by
  classical
  have hf : FiniteBlocks.fiber ({⟨a,r⟩} : Finset (BlockShape j h)) a = {r} := by
    ext s
    simp [FiniteBlocks.fiber]
  have hf' (b : BlockIndex h) (hba : b ≠ a) :
      FiniteBlocks.fiber ({⟨a,r⟩} : Finset (BlockShape j h)) b = ∅ := by
    ext s
    simp only [FiniteBlocks.fiber, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Finset.notMem_empty, iff_false]
    intro heq
    exact hba (congrArg Sigma.fst heq)
  unfold positiveShapeCoefficient
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), hf]
  have hprod : (∏ b ∈ (Finset.univ : Finset (BlockIndex h)).erase a,
      blockPolynomialCoefficient j b theta c (FiniteBlocks.fiber {⟨a,r⟩} b)) = 1 := by
    apply Finset.prod_eq_one
    intro b hb
    rw [hf' b (Finset.ne_of_mem_erase hb)]
    rfl
  rw [hprod, mul_one]
  simp [blockPolynomialCoefficient]

theorem shapeCoefficient_singleton (j : Fin d) (theta : ℝ)
    (a : BlockIndex h) (r : ShapesInBlock j a) :
    shapeCoefficient j theta {⟨a,r⟩} =
      (1/4:ℝ)*Walsh.coefficient (Walsh.smoothedBlock theta) {r} := by
  unfold shapeCoefficient
  rw [positiveShapeCoefficient_singleton, positiveShapeCoefficient_singleton]
  ring

/-- The block labels partition the actual shapes exactly once. -/
def blockShapeEquiv (j : Fin d) : BlockShape j h ≃ Dyadic.Shape d h :=
  Equiv.ofBijective (fun r => r.2.val) (by
    constructor
    · intro x y hxy
      rcases x with ⟨a, ⟨r, hr⟩⟩
      rcases y with ⟨b, ⟨s, hs⟩⟩
      change r = s at hxy
      subst s
      have hab : a = b := Subtype.ext (Fin.ext (hr.symm.trans hs))
      subst b
      rfl
    · intro r
      exact ⟨⟨shapeBlockIndex j r, ⟨r,rfl⟩⟩, rfl⟩)

/-- Exactly the blocks actually met by the selected shape set. -/
def activeBlocks (j : Fin d) (S : Finset (BlockShape j h)) : Finset (BlockIndex h) :=
  Finset.univ.filter (fun a => FiniteBlocks.fiber S a ≠ ∅)

lemma positiveShapeCoefficient_formula (j : Fin d) (theta c : ℝ)
    (S : Finset (BlockShape j h)) :
    positiveShapeCoefficient j theta c S = c^(activeBlocks j S).card *
      ∏ a ∈ activeBlocks j S, Walsh.coefficient (Walsh.smoothedBlock theta) (FiniteBlocks.fiber S a) := by
  classical
  have hprod : positiveShapeCoefficient j theta c S =
      ∏ a ∈ activeBlocks j S, blockPolynomialCoefficient j a theta c (FiniteBlocks.fiber S a) := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    have hf : FiniteBlocks.fiber S a = ∅ := by simpa [activeBlocks] using ha
    simp [blockPolynomialCoefficient, hf]
  rw [hprod]
  have ht (a : BlockIndex h) (ha : a ∈ activeBlocks j S) :
      blockPolynomialCoefficient j a theta c (FiniteBlocks.fiber S a) =
        c*Walsh.coefficient (Walsh.smoothedBlock theta) (FiniteBlocks.fiber S a) := by
    have hn : FiniteBlocks.fiber S a ≠ ∅ := (Finset.mem_filter.mp ha).2
    exact if_neg hn
  rw [Finset.prod_congr rfl ht, Finset.prod_mul_distrib, Finset.prod_const]

/-- Exact coefficient formula (4.4), before excluding zero even fibers. -/
theorem shapeCoefficient_formula (j : Fin d) (theta : ℝ)
    (S : Finset (BlockShape j h)) :
    shapeCoefficient j theta S = if Odd (activeBlocks j S).card then
      (1/4:ℝ)^(activeBlocks j S).card * ∏ a ∈ activeBlocks j S,
        Walsh.coefficient (Walsh.smoothedBlock theta) (FiniteBlocks.fiber S a) else 0 := by
  unfold shapeCoefficient
  rw [positiveShapeCoefficient_formula, positiveShapeCoefficient_formula,
    show (-1:ℝ)/4 = -((1:ℝ)/4) by ring]
  by_cases hodd : Odd (activeBlocks j S).card
  · rw [if_pos hodd, hodd.neg_pow]
    ring
  · have heven := Nat.not_odd_iff_even.mp hodd
    rw [if_neg hodd, heven.neg_pow]
    ring

theorem shapeCoefficient_eq_zero_of_even_fiber (j : Fin d) (theta : ℝ)
    (S : Finset (BlockShape j h)) (a : BlockIndex h)
    (ha : a ∈ activeBlocks j S) (heven : Even (FiniteBlocks.fiber S a).card) :
    shapeCoefficient j theta S = 0 := by
  have hf : FiniteBlocks.fiber S a ≠ ∅ := (Finset.mem_filter.mp ha).2
  have hz (c : ℝ) : positiveShapeCoefficient j theta c S = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp [blockPolynomialCoefficient, hf, Walsh.smoothedBlock_even_coefficient theta _ heven]
  unfold shapeCoefficient
  rw [hz, hz]
  norm_num

end Tusnady.Witness
