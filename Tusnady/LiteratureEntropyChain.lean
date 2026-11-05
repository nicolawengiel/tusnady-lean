import Tusnady.LiteratureEntropyPrefix

/-! # Differential entropy chain identity

This proves the formerly explicit literature input for the exact general
conditional-density system. Actual prefix densities telescope almost
everywhere; compact joint support and the stated entropy integrability
supply all needed Bochner integrability, without assuming marginal entropy
finiteness.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace Tusnady.LiteratureProof
set_option maxHeartbeats 1000000

theorem prefixLog_eq_sum_conditionalLog_ae {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) (n : ℕ) (hn : n ≤ M) :
    ∀ᵐ z ∂s.law,
      Real.log (prefixDensityN s n hn (takePrefix n hn z)) =
        ∑ i : Fin n, conditionalLogDensity s ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ z := by
  induction n with
  | zero =>
      exact Filter.Eventually.of_forall fun z => by
        simp only [prefixDensityN_zero, Real.log_one, Finset.univ_eq_empty,
          Finset.sum_empty]
  | succ n ih =>
      let j : Fin M := ⟨n, Nat.lt_of_succ_le hn⟩
      have hn0 : n ≤ M := Nat.le_of_succ_le hn
      filter_upwards [ih hn0, prefixLog_step_ae s j] with z hz hstep
      change Real.log (prefixDensityN s (n+1) hn (takePrefix (n+1) hn z)) = _ at hstep
      rw [hstep, hz, Fin.sum_univ_castSucc]
      rfl

/-- The logarithm of the actual joint density is the sum of the actual
conditional logarithms almost everywhere under the joint law. -/
theorem jointLog_eq_sum_conditionalLog_ae {M : ℕ} {f : (Fin M → ℝ) → ℝ}
    (s : ConditionalDensitySystem M f) :
    (fun z => Real.log (f z)) =ᵐ[s.law] (fun z => ∑ j, conditionalLogDensity s j z) := by
  have h := prefixLog_eq_sum_conditionalLog_ae s M le_rfl
  filter_upwards [h] with z hz
  have htake : takePrefix M (le_refl M) z = z := rfl
  simpa only [htake, prefixDensityN_full] using hz

/-- Complete proof of the general classical differential entropy chain input. -/
theorem conditionalEntropyChainIdentity : Literature.ConditionalEntropyChainIdentity := by
  intro M f s hH
  have hlog := jointLog_eq_sum_conditionalLog_ae s
  have hintegral := integral_congr_ae hlog
  have hchange : (∫ z, Real.log (f z) ∂s.law) = ∫ z, f z * Real.log (f z) :=
    integral_realDensityMeasure volume f _ s.joint_measurable s.joint_nonneg
  rw [hchange,
    integral_finset_sum _ (fun j _ => conditionalLogDensity_integrable s j (hH j))] at hintegral
  simp_rw [integral_conditionalLogDensity s _ (hH _)] at hintegral
  rw [Finset.sum_neg_distrib] at hintegral
  change (∑ j, ∫ z, s.entropyAt j z ∂s.law) = -(∫ z, f z * Real.log (f z))
  linarith

end Tusnady.LiteratureProof
