import Tusnady.LinearPrimitive
import Tusnady.HaarProjection

/-!
# Actual L2 vectors and squarefree orthogonality of W

The finite cell expansion constructs the actual L2 class of W. Distinct
cell choices yield distinct sets of variables, so the product-uniform
Parseval theorem applies to the actual cubic remainder.
-/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace Tusnady.Witness
variable {d h : ℕ} {j : Fin d}

/-- Genuine L2 class of the concrete cell product. -/
def cellL2Vector (G : CellIndex j h) : Lp ℝ 2 (Haar.cubeMeasure d) :=
  (cellFunction_memLp G.1 G.2).toLp (cellFunction G.1 G.2)

lemma cellL2Vector_ae (G : CellIndex j h) :
    cellL2Vector G =ᵐ[Haar.cubeMeasure d] cellFunction G.1 G.2 :=
  (cellFunction_memLp G.1 G.2).coeFn_toLp

/-- Genuine L2 vector of the actual manuscript W. -/
def testL2 (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) : Lp ℝ 2 (Haar.cubeMeasure d) :=
  ∑ G : CellIndex j h, (shapeCoefficient j theta G.1 * cellMonomial G.1 G.2 u) • cellL2Vector G

lemma testL2_ae (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) :
    testL2 j theta u =ᵐ[Haar.cubeMeasure d] testFunction j theta u := by
  have hs := Haar.finite_sum_ae (Finset.univ : Finset (CellIndex j h))
    (fun G => (shapeCoefficient j theta G.1 * cellMonomial G.1 G.2 u) • cellL2Vector G)
    (fun G x => shapeCoefficient j theta G.1 * cellMonomial G.1 G.2 u * cellFunction G.1 G.2 x)
    (fun G _ => by
      filter_upwards [Lp.coeFn_smul (shapeCoefficient j theta G.1 * cellMonomial G.1 G.2 u)
        (cellL2Vector G), cellL2Vector_ae G] with x hsmul hG
      exact hsmul.trans (congrArg (fun t => (shapeCoefficient j theta G.1 * cellMonomial G.1 G.2 u)*t) hG))
  filter_upwards [hs] with x hx
  unfold testL2
  rw [hx, Fintype.sum_sigma]
  exact (testFunction_cellExpansion j theta u x).symm

lemma continuous_testL2 (j : Fin d) (theta : ℝ) :
    Continuous (testL2 (h := h) j theta) := by
  apply continuous_finset_sum
  intro G _
  exact (continuous_const.mul (cellMonomial_continuous G.1 G.2)).smul continuous_const

def cubicCoefficient (j : Fin d) (theta : ℝ) (G : CellIndex j h) : ℝ :=
  if 3 ≤ G.1.card then shapeCoefficient j theta G.1 else 0

def cubicTestL2 (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) : Lp ℝ 2 (Haar.cubeMeasure d) :=
  ∑ G : CellIndex j h, (cubicCoefficient j theta G * cellMonomial G.1 G.2 u) • cellL2Vector G

lemma cubicTestL2_ae (j : Fin d) (theta : ℝ) (u : Shell d h → ℝ) :
    cubicTestL2 j theta u =ᵐ[Haar.cubeMeasure d]
      (fun x => testFunction j theta u x - linearTestFunction j theta u x) := by
  have hs := Haar.finite_sum_ae (Finset.univ : Finset (CellIndex j h))
    (fun G => (cubicCoefficient j theta G * cellMonomial G.1 G.2 u) • cellL2Vector G)
    (fun G x => cubicCoefficient j theta G * cellMonomial G.1 G.2 u * cellFunction G.1 G.2 x)
    (fun G _ => by
      filter_upwards [Lp.coeFn_smul (cubicCoefficient j theta G * cellMonomial G.1 G.2 u)
        (cellL2Vector G), cellL2Vector_ae G] with x hsmul hG
      exact hsmul.trans (congrArg (fun t => (cubicCoefficient j theta G * cellMonomial G.1 G.2 u)*t) hG))
  filter_upwards [hs] with x hx
  unfold cubicTestL2
  rw [hx, Fintype.sum_sigma, testFunction_sub_linear_cellExpansion]
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro c _
  by_cases hS : 3 ≤ S.card <;> simp [cubicCoefficient, hS]

/-- Main.pdf (4.6) for the actual cubic remainder and any bounded linear
operator on the genuine L2 space. No moment or monomial assumption. -/
theorem expected_cubic_operator_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (j : Fin d) (theta : ℝ) (O : Lp ℝ 2 (Haar.cubeMeasure d) →L[ℝ] E) :
    (∫ u, ‖O (cubicTestL2 j theta u)‖^2 ∂UniformMonomial.cubeLaw (Shell d h)) =
      ∑ G : CellIndex j h, cubicCoefficient j theta G^2 *
        (1/3:ℝ)^(variableSet G).card * ‖O (cellL2Vector G)‖^2 := by
  have heq (u : Shell d h → ℝ) : O (cubicTestL2 j theta u) =
      ∑ G : CellIndex j h,
        (cubicCoefficient j theta G * UniformMonomial.monomial (variableSet G) u) • O (cellL2Vector G) := by
    simp only [cubicTestL2, map_sum, map_smul, cellMonomial, variableSet, UniformMonomial.monomial]
  simp_rw [heq]
  exact UniformMonomial.finite_parseval_weighted variableSet (variableSet_injective j h)
    (cubicCoefficient j theta) (fun G => O (cellL2Vector G))

end Tusnady.Witness
