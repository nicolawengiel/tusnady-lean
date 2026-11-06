import Tusnady.Upper.CompactGaussianBody
import Tusnady.Upper.PrefixSmallRadius
import Tusnady.Upper.OrthantPrefixFactorization
import Tusnady.Upper.OrthantPrefixBalancing
import Tusnady.Upper.Conclusions

/-!
# Nikolov's reduction with a conservative universal signing constant

The universal signing factor is 1000. All finite geometry, norm estimates, Gaussian tails, compactification, prefix
selection and changes of quantifiers are discharged here.  Every result retains
`SmallGaussianFoldMonotonicity` as an explicit argument. Its proof is supplied
by `Ehrhard.VerticalFoldMonotonicity` and instantiated in `Upper.Main`.
No new axiom, placeholder proof or implicit literature assumption is introduced.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.Upper

/-- One real coloring controls every query and every prefix simultaneously.
The separately proved analytic input is displayed in the first argument. -/
theorem query_prefix_signing_of_smallGaussianFoldMonotonicity
    (hfold : SmallGaussianFoldMonotonicity) {s N k : ℕ} (hN : 0 < N)
    (U : DyadicFactorization.Query s N → EuclideanSpace ℝ (Fin k))
    (V : Fin N → EuclideanSpace ℝ (Fin k))
    {B : ℝ} (hB : 0 < B) (hU : ∀ q, ‖U q‖ ≤ B) (hV : ∀ i, ‖V i‖ ≤ 1) :
    ∃ χ : Fin N → ℝ, IsSignColoring χ ∧
      ∀ q (m : Fin (N+1)), |inner ℝ (U q) (finitePrefix V χ m)| ≤
        1000 * (B * Real.sqrt (2 * Real.log (gaussianTailScale s N))) := by
  obtain ⟨K, hKcomp, hKconv, hKsymm, hKzero, hKmass, hKslabs⟩ :=
    exists_compact_query_body hN U hB hU
  obtain ⟨χ, hχprefix⟩ := prefix_signing_of_smallGaussianFoldMonotonicity hfold hN
    K hKcomp hKconv hKsymm hKmass V hV
  let K1000 := (fun z : EuclideanSpace ℝ (Fin k) => (1000 : ℝ) • z) '' K
  have hK1000zero : (0 : EuclideanSpace ℝ (Fin k)) ∈ K1000 := ⟨0, hKzero, by simp⟩
  obtain ⟨hχ, hpref⟩ := real_finitePrefix_mem_of_fin_signs V χ K1000 hK1000zero hχprefix
  refine ⟨fun i => Tusnady.sign (χ i), hχ, ?_⟩
  intro q m
  obtain ⟨z, hz, heq⟩ := hpref m
  rw [← heq, inner_smul_right, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1000)]
  exact mul_le_mul_of_nonneg_left (hKslabs hz q) (by norm_num)

/-- Explicit dimension-only constant; no sample size occurs in its definition. -/
def smallRadiusNikolovConstant (s : ℕ) : ℝ :=
  1000 * DyadicFactorization.factorConstant s * Real.sqrt (2 * ((s : ℝ)+4))

lemma smallRadiusNikolovConstant_pos (s : ℕ) : 0 < smallRadiusNikolovConstant s := by
  unfold smallRadiusNikolovConstant
  exact mul_pos (mul_pos (by norm_num) (DyadicFactorization.factorConstant_pos s))
    (Real.sqrt_pos.mpr (by positivity))

/-- The final geometric coloring bound.  Repetitions are allowed in this
stronger indexed statement; one coloring works for all full-dimensional closed
lower orthants. The separately proved analytic premise remains visible. -/
theorem orthant_coloring_of_smallGaussianFoldMonotonicity
    (hfold : SmallGaussianFoldMonotonicity) {s N : ℕ} (hN : 0 < N)
    (P : Fin N → Point (s+1)) :
    ∃ χ : Fin N → ℝ, IsSignColoring χ ∧ ∀ x : Point (s+1),
      |realAnchoredCount P χ x| ≤ smallRadiusNikolovConstant s * upperGrowth (s+1) N := by
  apply coloring_of_dyadic_prefix_signing P
  intro k U V hV hU
  have hB : 0 < DyadicFactorization.factorConstant s * (Real.log ((N : ℝ)+2))^s :=
    mul_pos (DyadicFactorization.factorConstant_pos s) (pow_pos (log_sample_pos N) s)
  obtain ⟨χ, hχ, hpref⟩ := query_prefix_signing_of_smallGaussianFoldMonotonicity hfold hN
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
    (by norm_num : (0 : ℝ) ≤ 1000)
  rw [hgrowth] at hthreshold
  simpa only [smallRadiusNikolovConstant, mul_assoc] using hthreshold

end Tusnady.Upper

namespace Tusnady
open Upper

/-- A fully proved implication, not the requested unconditional main theorem.
The analytic argument is explicit here and is supplied in `Upper.Main`. -/
theorem upperBound_of_smallGaussianFoldMonotonicity (hfold : SmallGaussianFoldMonotonicity) :
    HigherDimensionalUpperBound := by
  apply upperBound_of_positive_cardinality
  intro d hd
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 by omega)
  refine ⟨smallRadiusNikolovConstant s, smallRadiusNikolovConstant_pos s, ?_⟩
  intro N hN
  apply (worstDiscrepancy_le_iff_real_colorings (by omega) N _).mpr
  intro P _
  exact orthant_coloring_of_smallGaussianFoldMonotonicity hfold hN P

theorem coloringUpperBound_of_smallGaussianFoldMonotonicity (hfold : SmallGaussianFoldMonotonicity) :
    ColoringUpperBound :=
  upper_iff_coloringUpperBound.mp (upperBound_of_smallGaussianFoldMonotonicity hfold)

theorem asymptoticUpperBound_of_smallGaussianFoldMonotonicity (hfold : SmallGaussianFoldMonotonicity) :
    AsymptoticUpperBound :=
  upperBound_implies_asymptotic (upperBound_of_smallGaussianFoldMonotonicity hfold)

theorem sharpOrder_of_smallGaussianFoldMonotonicity (hfold : SmallGaussianFoldMonotonicity) :
    SharpHigherDimensionalOrder :=
  sharpOrder_of_upperBound (upperBound_of_smallGaussianFoldMonotonicity hfold)

end Tusnady
