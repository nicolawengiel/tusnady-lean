import Tusnady.Upper.CompactGaussianBody
import Tusnady.Upper.PrefixGaussian
import Tusnady.Upper.OrthantPrefixFactorization
import Tusnady.Upper.OrthantPrefixBalancing
import Tusnady.Upper.Conclusions

/-!
# Nikolov's complete reduction to the precisely named open analytic theorem

All finite geometry, norm estimates, Gaussian tails, compactification, prefix
selection and changes of quantifiers are discharged here.  Every result retains
`GaussianFoldMonotonicity` as an explicit premise.  That proposition is still
OPEN, so none of these declarations is the unconditional upper main theorem.
No new axiom, placeholder proof or implicit literature assumption is introduced.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.Upper

/-- One real coloring controls every query and every prefix simultaneously.
The only unfinished analytic input is displayed in the first argument. -/
theorem query_prefix_signing_of_gaussianFoldMonotonicity
    (hfold : GaussianFoldMonotonicity) {s N k : ℕ} (hN : 0 < N)
    (U : DyadicFactorization.Query s N → EuclideanSpace ℝ (Fin k))
    (V : Fin N → EuclideanSpace ℝ (Fin k))
    {B : ℝ} (hB : 0 < B) (hU : ∀ q, ‖U q‖ ≤ B) (hV : ∀ i, ‖V i‖ ≤ 1) :
    ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
      ∀ q (m : Fin (N+1)), |inner ℝ (U q) (finitePrefix V χ m)| ≤
        5 * (B * Real.sqrt (2 * Real.log (gaussianTailScale s N))) := by
  obtain ⟨K, hKcomp, hKconv, hKsymm, hKzero, hKmass, hKslabs⟩ :=
    exists_compact_query_body hN U hB hU
  obtain ⟨χ, hχprefix⟩ := prefix_signing_of_gaussianFoldMonotonicity hfold hN
    K hKcomp hKconv hKsymm hKmass V hV
  let K5 := (fun z : EuclideanSpace ℝ (Fin k) => (5 : ℝ) • z) '' K
  have hK5zero : (0 : EuclideanSpace ℝ (Fin k)) ∈ K5 := ⟨0, hKzero, by simp⟩
  obtain ⟨hχ, hpref⟩ := real_finitePrefix_mem_of_fin_signs V χ K5 hK5zero hχprefix
  refine ⟨fun i => Tusnady.sign (χ i), hχ, ?_⟩
  intro q m
  obtain ⟨z, hz, heq⟩ := hpref m
  rw [← heq, inner_smul_right, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5)]
  exact mul_le_mul_of_nonneg_left (hKslabs hz q) (by norm_num)

/-- Explicit dimension-only constant; no sample size occurs in its definition. -/
def nikolovConstant (s : ℕ) : ℝ :=
  5 * DyadicFactorization.factorConstant s * Real.sqrt (2 * ((s : ℝ)+4))

lemma nikolovConstant_pos (s : ℕ) : 0 < nikolovConstant s := by
  unfold nikolovConstant
  exact mul_pos (mul_pos (by norm_num) (DyadicFactorization.factorConstant_pos s))
    (Real.sqrt_pos.mpr (by positivity))

/-- The final geometric coloring bound.  Repetitions are allowed in this
stronger indexed statement; one coloring works for all full-dimensional closed
lower orthants.  The open analytic premise remains visible. -/
theorem orthant_coloring_of_gaussianFoldMonotonicity
    (hfold : GaussianFoldMonotonicity) {s N : ℕ} (hN : 0 < N)
    (P : Fin N → Point (s+1)) :
    ∃ χ : Fin N → ℝ, IsSignColoring χ ∧ ∀ x : Point (s+1),
      |realAnchoredCount P χ x| ≤ nikolovConstant s * upperGrowth (s+1) N := by
  apply coloring_of_dyadic_prefix_signing P
  intro k U V hV hU
  have hB : 0 < DyadicFactorization.factorConstant s * (Real.log ((N : ℝ)+2))^s :=
    mul_pos (DyadicFactorization.factorConstant_pos s) (pow_pos (log_sample_pos N) s)
  obtain ⟨χ, hχ, hpref⟩ := query_prefix_signing_of_gaussianFoldMonotonicity hfold hN
    U V hB hU hV
  refine ⟨χ, hχ, fun q m => (hpref q m).trans ?_⟩
  have hgrowth : (Real.log ((N : ℝ)+2))^((s : ℝ)+(1 : ℝ)/2) = upperGrowth (s+1) N := by
    unfold upperGrowth
    congr 1
    · congr 1
      ring
    · push_cast
      ring
  have hthreshold := mul_le_mul_of_nonneg_left (dyadic_gaussianThreshold_le s N hN)
    (by norm_num : (0 : ℝ) ≤ 5)
  rw [hgrowth] at hthreshold
  simpa only [nikolovConstant, mul_assoc] using hthreshold

end Tusnady.Upper

namespace Tusnady
open Upper

/-- A fully proved implication, not the requested unconditional main theorem.
The exact outstanding analytic premise cannot disappear from its type. -/
theorem upperBound_of_gaussianFoldMonotonicity (hfold : GaussianFoldMonotonicity) :
    HigherDimensionalUpperBound := by
  apply upperBound_of_positive_cardinality
  intro d hd
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  refine ⟨nikolovConstant s, nikolovConstant_pos s, ?_⟩
  intro N hN
  apply (worstDiscrepancy_le_iff_real_colorings (by omega) N _).mpr
  intro P _
  exact orthant_coloring_of_gaussianFoldMonotonicity hfold hN P

theorem coloringUpperBound_of_gaussianFoldMonotonicity (hfold : GaussianFoldMonotonicity) :
    ColoringUpperBound :=
  upper_iff_coloringUpperBound.mp (upperBound_of_gaussianFoldMonotonicity hfold)

theorem asymptoticUpperBound_of_gaussianFoldMonotonicity (hfold : GaussianFoldMonotonicity) :
    AsymptoticUpperBound :=
  upperBound_implies_asymptotic (upperBound_of_gaussianFoldMonotonicity hfold)

theorem sharpOrder_of_gaussianFoldMonotonicity (hfold : GaussianFoldMonotonicity) :
    SharpHigherDimensionalOrder :=
  sharpOrder_of_upperBound (upperBound_of_gaussianFoldMonotonicity hfold)

end Tusnady
