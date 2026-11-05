import Tusnady.BlockPolynomial

/-!
# Actual cell monomials of W

Every selected shape contributes exactly one actual shell box. The index
set is finite and the map to squarefree sets of shell variables is injective.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
variable {d h : ℕ} {j : Fin d}

abbrev CellChoice (S : Finset (BlockShape j h)) : Type :=
  (r : S) → Dyadic.CellIndices r.val.2.val.depth

def chosenShell (S : Finset (BlockShape j h)) (c : CellChoice S) (r : S) : Shell d h :=
  ⟨r.val.2.val, c r⟩

lemma chosenShell_injective (S : Finset (BlockShape j h)) (c : CellChoice S) :
    Function.Injective (chosenShell S c) := by
  intro r s hrs
  apply Subtype.ext
  apply (blockShapeEquiv j).injective
  exact congrArg Sigma.fst hrs

def chosenSet (S : Finset (BlockShape j h)) (c : CellChoice S) : Finset (Shell d h) :=
  Finset.univ.image (chosenShell S c)

lemma card_chosenSet (S : Finset (BlockShape j h)) (c : CellChoice S) :
    (chosenSet S c).card = S.card := by
  rw [chosenSet, Finset.card_image_of_injective _ (chosenShell_injective S c)]
  simp

lemma prod_chosenSet (S : Finset (BlockShape j h)) (c : CellChoice S) (f : Shell d h → ℝ) :
    (∏ R ∈ chosenSet S c, f R) = ∏ r : S, f (chosenShell S c r) := by
  unfold chosenSet
  rw [Finset.prod_image]
  intro r _ s _ hrs
  exact chosenShell_injective S c hrs

/-- The actual coefficient monomial, squarefree in shell variables. -/
def cellMonomial (S : Finset (BlockShape j h)) (c : CellChoice S) (u : Shell d h → ℝ) : ℝ :=
  ∏ R ∈ chosenSet S c, u R

/-- The actual physical tensor product for a cell monomial. -/
def cellFunction (S : Finset (BlockShape j h)) (c : CellChoice S) (x : Point d) : ℝ :=
  ∏ R ∈ chosenSet S c, qShell R x

theorem product_layers_expansion (S : Finset (BlockShape j h)) (u : Shell d h → ℝ)
    (x : Point d) :
    (∏ r ∈ S, layer r.2.val u x) =
      ∑ c : CellChoice S, cellMonomial S c u * cellFunction S c x := by
  classical
  rw [← Finset.prod_coe_sort S]
  simp only [layer]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [cellMonomial, cellFunction, prod_chosenSet, prod_chosenSet,
    Finset.prod_mul_distrib]
  rfl

/-- Full actual finite cell-monomial expansion of the W used in duality. -/
theorem testFunction_cellExpansion (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) :
    testFunction j theta u x = ∑ S : Finset (BlockShape j h),
      ∑ c : CellChoice S, shapeCoefficient j theta S * cellMonomial S c u * cellFunction S c x := by
  classical
  rw [testFunction_shapeExpansion]
  apply Finset.sum_congr rfl
  intro S _
  rw [product_layers_expansion, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Recover all shape labels from the actual set of shell variables. -/
lemma chosenSet_recover_shapes (S : Finset (BlockShape j h)) (c : CellChoice S) :
    (chosenSet S c).image (fun R => (blockShapeEquiv j).symm R.1) = S := by
  classical
  calc
    _ = (Finset.univ : Finset S).image (fun r => r.val) := by
      rw [chosenSet, Finset.image_image]
      congr 1
      funext r
      exact (blockShapeEquiv j).symm_apply_apply r.val
    _ = S := by
      rw [Finset.univ_eq_attach, Finset.attach_image_val]

abbrev CellIndex (j : Fin d) (h : ℕ) := (S : Finset (BlockShape j h)) × CellChoice S

def variableSet (G : CellIndex j h) : Finset (Shell d h) := chosenSet G.1 G.2

/-- Distinct actual cell choices give distinct squarefree monomials. -/
theorem variableSet_injective (j : Fin d) (h : ℕ) :
    Function.Injective (variableSet : CellIndex j h → Finset (Shell d h)) := by
  classical
  intro G G' hGG
  rcases G with ⟨S,c⟩
  rcases G' with ⟨S',c'⟩
  have hS : S = S' := by
    have hh := congrArg (Finset.image (fun R : Shell d h => (blockShapeEquiv j).symm R.1)) hGG
    simpa only [variableSet, chosenSet_recover_shapes] using hh
  subst S'
  change chosenSet S c = chosenSet S c' at hGG
  have hc : c = c' := by
    funext r
    have hr : chosenShell S c r ∈ chosenSet S c' := by
      rw [← hGG]
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩
    obtain ⟨s, _, hs⟩ := Finset.mem_image.mp hr
    have hsr : s = r := by
      apply Subtype.ext
      apply (blockShapeEquiv j).injective
      exact congrArg Sigma.fst hs
    subst s
    have hsecond : c' r = c r := eq_of_heq (Sigma.mk.inj hs).2
    exact hsecond.symm
  subst c'
  rfl

end Tusnady.Witness
