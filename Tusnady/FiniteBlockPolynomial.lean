import Tusnady.TestFunction
import Mathlib.Data.Finset.Sigma

/-!
# Explicit polynomial expansion over disjoint finite blocks

Subsets of the disjoint union correspond exactly to one subset in every
block. This finite equivalence supplies the full coefficient expansion;
no formal power-series or convergence assumptions are involved.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.FiniteBlocks
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {B : A → Type*} [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]

def fiber (S : Finset (Σ a, B a)) (a : A) : Finset (B a) :=
  Finset.univ.filter (fun b => (⟨a,b⟩ : Σ a, B a) ∈ S)

def assemble (t : (a : A) → Finset (B a)) : Finset (Σ a, B a) :=
  Finset.univ.sigma t

@[simp] theorem fiber_assemble (t : (a : A) → Finset (B a)) (a : A) :
    fiber (assemble t) a = t a := by
  ext b
  simp [fiber, assemble]

@[simp] theorem assemble_fiber (S : Finset (Σ a, B a)) : assemble (fiber S) = S := by
  ext ⟨a,b⟩
  simp [assemble, fiber]

/-- Exact finite equivalence, including empty fibers. -/
def subsetsEquiv : ((a : A) → Finset (B a)) ≃ Finset (Σ a, B a) where
  toFun := assemble
  invFun := fiber
  left_inv t := funext (fiber_assemble t)
  right_inv := assemble_fiber

/-- Multiplying the block polynomials gives one squarefree monomial for
every subset of the disjoint union, with the actual product coefficient. -/
theorem product_expansion (C : (a : A) → Finset (B a) → ℝ)
    (y : (Σ a, B a) → ℝ) :
    (∏ a, ∑ T : Finset (B a), C a T * ∏ b ∈ T, y ⟨a,b⟩) =
      ∑ S : Finset (Σ a, B a), (∏ a, C a (fiber S a)) * ∏ r ∈ S, y r := by
  rw [Fintype.prod_sum]
  symm
  rw [← subsetsEquiv.sum_comp
    (fun S : Finset (Σ a, B a) => (∏ a, C a (fiber S a)) * ∏ r ∈ S, y r)]
  apply Finset.sum_congr rfl
  intro t _
  change (∏ a, C a (fiber (assemble t) a)) *
    (∏ r ∈ Finset.univ.sigma t, y r) = _
  simp only [fiber_assemble, Finset.prod_sigma, Finset.prod_mul_distrib]

end Tusnady.FiniteBlocks
