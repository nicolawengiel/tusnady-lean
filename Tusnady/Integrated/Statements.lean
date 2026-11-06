import Tusnady.Upper.Statements
import Tusnady.Boxes.Corners

/-!
Exact integration targets. Constants are chosen after the dimension and
before the cardinality. All configurations contain exactly N distinct points.
The original discrepancy and growth definitions are used unchanged.
-/
namespace Tusnady.Integrated

def LowerBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → c * targetGrowth d N ≤ Tusnady.worstDiscrepancy d N

def SharpOrder : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * targetGrowth d N ≤ Tusnady.worstDiscrepancy d N ∧
        Tusnady.worstDiscrepancy d N ≤ C * targetGrowth d N

def BoxSharpOrder : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * targetGrowth d N ≤ Boxes.worstDiscrepancy d N ∧
        Boxes.worstDiscrepancy d N ≤ C * targetGrowth d N

/-- One theorem states the lower bound, the range comparison, and the upper
bound for general closed bounded axis-parallel boxes. Thus the same c,C and
threshold also bound the closed lower orthants in that dimension. -/
def CombinedSharpOrder : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      c * targetGrowth d N ≤ Tusnady.worstDiscrepancy d N ∧
        Tusnady.worstDiscrepancy d N ≤ Boxes.worstDiscrepancy d N ∧
          Boxes.worstDiscrepancy d N ≤ C * targetGrowth d N

/-- The coloring controls the existing `Box a b` for every pair of finite real
corners, with no order restriction; an invalid pair gives the empty box. -/
def BoxColoringUpperBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ N : ℕ, ∀ P : Fin N → Point d, Function.Injective P →
      ∃ χ : Fin N → ℝ, IsSignColoring χ ∧ ∀ a b : Point d,
        |Boxes.realCountCorners P χ a b| ≤ C * upperGrowth d N

def BoxWitnessLowerBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
    ∀ N : ℕ, N₀ ≤ N → ∃ P : Fin N → Point d, Function.Injective P ∧
      ∀ χ : Fin N → ℝ, IsSignColoring χ → ∃ a b : Point d,
        (∀ j, a j ≤ b j) ∧ c * targetGrowth d N ≤ |Boxes.realCountCorners P χ a b|

end Tusnady.Integrated
