import Tusnady.SamplingSpaceDyadic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Canonical pointwise representatives of the genuine L² affine space

The L² space is the span of the proved orthonormal dyadic affine basis.
A separate, injective pointwise synthesis supplies its canonical actual
functions. Evaluations below never evaluate arbitrary L² representatives.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

abbrev L2Real := Lp ℝ 2 (volume : Measure ℝ)

def basisL2 (j : ℕ) (ib : BasisIndex j) : L2Real :=
  (basis_memLp j ib).toLp (basis j ib)

lemma basisL2_ae (j : ℕ) (ib : BasisIndex j) : basisL2 j ib =ᵐ[volume] basis j ib :=
  (basis_memLp j ib).coeFn_toLp

theorem basisL2_inner (j : ℕ) (ib kc : BasisIndex j) :
    inner ℝ (basisL2 j ib) (basisL2 j kc) = if ib = kc then 1 else 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, basis j ib x * basis j kc x := by
      apply integral_congr_ae
      filter_upwards [basisL2_ae j ib, basisL2_ae j kc] with x hib hkc
      rw [hib, hkc]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    _ = _ := basis_inner j ib kc

theorem basisL2_orthonormal (j : ℕ) : Orthonormal ℝ (basisL2 j) := by
  classical
  exact orthonormal_iff_ite.mpr (basisL2_inner j)

/-- Actual pointwise synthesis, as a linear map into real functions. -/
def pointwiseSynthesis (j : ℕ) : (BasisIndex j → ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
  Fintype.linearCombination ℝ (basis j)

/-- Corresponding synthesis in genuine L². -/
def l2Synthesis (j : ℕ) : (BasisIndex j → ℝ) →ₗ[ℝ] L2Real :=
  Fintype.linearCombination ℝ (basisL2 j)

lemma pointwiseSynthesis_apply (j : ℕ) (a : BasisIndex j → ℝ) (x : ℝ) :
    pointwiseSynthesis j a x = ∑ ib, a ib * basis j ib x := by
  simp [pointwiseSynthesis, Fintype.linearCombination_apply, Finset.sum_apply]

/-- The actual pointwise synthesis agrees almost everywhere with its L²
class. The finite-sum coercion is proved explicitly. -/
theorem l2Synthesis_ae (j : ℕ) (a : BasisIndex j → ℝ) :
    l2Synthesis j a =ᵐ[volume] pointwiseSynthesis j a := by
  classical
  have hsum : ∀ S : Finset (BasisIndex j),
      (∑ ib ∈ S, a ib • basisL2 j ib : L2Real) =ᵐ[volume]
        (fun x => ∑ ib ∈ S, a ib * basis j ib x) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      filter_upwards [Lp.coeFn_zero ℝ 2 (volume : Measure ℝ)] with x hx
      simpa only [Finset.sum_empty, Pi.zero_apply] using hx
    | @insert ib S hib ih =>
      simp only [Finset.sum_insert hib]
      filter_upwards [Lp.coeFn_add (a ib • basisL2 j ib) (∑ kc ∈ S, a kc • basisL2 j kc),
        Lp.coeFn_smul (a ib) (basisL2 j ib), basisL2_ae j ib, ih] with x hadd hsmul hb hrest
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsmul
      rw [hadd, hsmul, hb, hrest]
  have hp : pointwiseSynthesis j a = (fun x => ∑ ib, a ib * basis j ib x) :=
    funext (pointwiseSynthesis_apply j a)
  rw [hp]
  simpa only [l2Synthesis, Fintype.linearCombination_apply] using hsum Finset.univ

theorem l2Synthesis_injective (j : ℕ) : Function.Injective (l2Synthesis j) :=
  (basisL2_orthonormal j).linearIndependent.fintypeLinearCombination_injective

theorem pointwiseSynthesis_injective (j : ℕ) : Function.Injective (pointwiseSynthesis j) := by
  intro a b hab
  apply l2Synthesis_injective j
  apply Lp.ext
  exact (l2Synthesis_ae j a).trans (hab ▸ (l2Synthesis_ae j b).symm)

/-- Finite-dimensional space of actual, canonical pointwise functions. -/
def pointwiseSpace (j : ℕ) : Submodule ℝ (ℝ → ℝ) :=
  LinearMap.range (pointwiseSynthesis j)

/-- The actual finite-dimensional subspace of L². -/
def l2Space (j : ℕ) : Submodule ℝ L2Real :=
  Submodule.span ℝ (Set.range (basisL2 j))

theorem l2Space_eq_range (j : ℕ) : l2Space j = LinearMap.range (l2Synthesis j) :=
  (Fintype.range_linearCombination ℝ (basisL2 j)).symm

instance pointwiseSpace_finiteDimensional (j : ℕ) : FiniteDimensional ℝ (pointwiseSpace j) :=
  LinearMap.finiteDimensional_range _

instance l2Space_finiteDimensional (j : ℕ) : FiniteDimensional ℝ (l2Space j) := by
  rw [l2Space_eq_range]
  infer_instance

theorem pointwiseSpace_finrank (j : ℕ) : Module.finrank ℝ (pointwiseSpace j) = 2 ^ (j + 1) := by
  rw [pointwiseSpace, LinearMap.finrank_range_of_inj (pointwiseSynthesis_injective j)]
  simp [BasisIndex, pow_succ]

theorem l2Space_finrank (j : ℕ) : Module.finrank ℝ (l2Space j) = 2 ^ (j + 1) := by
  rw [l2Space, finrank_span_eq_card (basisL2_orthonormal j).linearIndependent, basisIndex_card]

/-- Each L² element has exactly one coefficient vector in the actual
pointwise basis. This prevents evaluations of arbitrary equivalence classes. -/
theorem existsUnique_l2_coefficients (j : ℕ) (v : l2Space j) :
    ∃! a : BasisIndex j → ℝ, l2Synthesis j a = (v : L2Real) := by
  have hv : (v : L2Real) ∈ LinearMap.range (l2Synthesis j) := by
    rw [← l2Space_eq_range]
    exact v.property
  obtain ⟨a, ha⟩ := hv
  exact ⟨a, ha, fun b hb => l2Synthesis_injective j (hb.trans ha.symm)⟩

def canonicalCoefficients (j : ℕ) (v : l2Space j) : BasisIndex j → ℝ :=
  Classical.choose (existsUnique_l2_coefficients j v)

def canonicalRepresentative (j : ℕ) (v : l2Space j) : ℝ → ℝ :=
  pointwiseSynthesis j (canonicalCoefficients j v)

theorem canonicalRepresentative_ae (j : ℕ) (v : l2Space j) :
    (v : L2Real) =ᵐ[volume] canonicalRepresentative j v := by
  have h := (Classical.choose_spec (existsUnique_l2_coefficients j v)).1
  rw [← h]
  exact l2Synthesis_ae j (canonicalCoefficients j v)

end Tusnady.SamplingSpace
