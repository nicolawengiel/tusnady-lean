import Tusnady.LiteratureSamplingBasic
import Mathlib.Probability.Independence.Integration

/-! Actual finite iid preliminary sampling, before the unresolved O(D)
frame selection. The mean-square calculation uses genuine product measures.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal
namespace Tusnady.LiteratureSampling

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

def sampleLaw (m : ℕ) : Measure (Fin m → X) := Measure.pi (fun _ : Fin m => μ)

instance sampleLaw_probability (m : ℕ) : IsProbabilityMeasure (sampleLaw μ m) := by
  unfold sampleLaw
  infer_instance

lemma coordinate_integral (m : ℕ) (g : X → ℝ) (hg : AEStronglyMeasurable g μ) (j : Fin m) :
    (∫ x, g (x j) ∂sampleLaw μ m) = ∫ x, g x ∂μ := by
  have hp : MeasurePreserving (fun x : Fin m → X => x j) (sampleLaw μ m) μ :=
    measurePreserving_eval (fun _ : Fin m => μ) j
  have hg' : AEStronglyMeasurable g ((sampleLaw μ m).map (fun x => x j)) := by
    rwa [hp.map_eq]
  have ht := integral_map hp.measurable.aemeasurable hg'
  rw [hp.map_eq] at ht
  exact ht.symm

lemma coordinate_memLp (m : ℕ) (g : X → ℝ) (hg : MemLp g 2 μ) (j : Fin m) :
    MemLp (fun x : Fin m → X => g (x j)) 2 (sampleLaw μ m) :=
  hg.comp_measurePreserving (measurePreserving_eval (fun _ : Fin m => μ) j)

lemma coordinate_mixed_integral (m : ℕ) (g : X → ℝ) (hg : Measurable g)
    (hzero : (∫ x, g x ∂μ) = 0) (j k : Fin m) (hjk : j ≠ k) :
    (∫ x : Fin m → X, g (x j) * g (x k) ∂sampleLaw μ m) = 0 := by
  have hind : IndepFun (fun x : Fin m → X => g (x j)) (fun x => g (x k)) (sampleLaw μ m) := (iIndepFun_pi (μ := fun _ : Fin m => μ) (X := fun _ : Fin m => g) (fun _ => hg.aemeasurable)).indepFun hjk
  rw [hind.integral_fun_mul_eq_mul_integral
    (hg.comp (measurable_pi_apply j)).aestronglyMeasurable
    (hg.comp (measurable_pi_apply k)).aestronglyMeasurable,
    coordinate_integral μ m g hg.aestronglyMeasurable j,
    coordinate_integral μ m g hg.aestronglyMeasurable k, hzero, zero_mul]

/-- The actual iid cancellation of every mixed summand. -/
theorem integral_sum_coordinate_sq (m : ℕ) (g : X → ℝ) (hg : Measurable g)
    (hgp : MemLp g 2 μ) (hzero : (∫ x, g x ∂μ) = 0) :
    (∫ x : Fin m → X, (∑ j, g (x j)) ^ 2 ∂sampleLaw μ m) =
      (m : ℝ) * ∫ x, g x ^ 2 ∂μ := by
  classical
  have hi : ∀ j k : Fin m, Integrable (fun x : Fin m → X => g (x j) * g (x k))
      (sampleLaw μ m) := fun j k => (coordinate_memLp μ m g hgp j).integrable_mul
        (coordinate_memLp μ m g hgp k)
  have he (x : Fin m → X) : (∑ j, g (x j)) ^ 2 = ∑ j, ∑ k, g (x j) * g (x k) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  simp_rw [he]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hi j k))]
  simp_rw [integral_finset_sum _ (fun k _ => hi _ k)]
  have hentry (j k : Fin m) :
      (∫ x : Fin m → X, g (x j) * g (x k) ∂sampleLaw μ m) =
        if j = k then (∫ x, g x ^ 2 ∂μ) else 0 := by
    by_cases hjk : j = k
    · subst k
      rw [if_pos rfl]
      simpa only [← pow_two] using coordinate_integral μ m (fun x => g x * g x)
        (hg.mul hg).aestronglyMeasurable j
    · rw [if_neg hjk]
      exact coordinate_mixed_integral μ m g hg hzero j k hjk
  simp only [hentry, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem integral_average_coordinate_sq (m : ℕ) (hm : 0 < m) (g : X → ℝ)
    (hg : Measurable g) (hgp : MemLp g 2 μ) (hzero : (∫ x, g x ∂μ) = 0) :
    (∫ x : Fin m → X, ((∑ j, g (x j)) / m) ^ 2 ∂sampleLaw μ m) =
      (∫ x, g x ^ 2 ∂μ) / m := by
  simp_rw [div_pow]
  rw [integral_div, integral_sum_coordinate_sq μ m g hg hgp hzero]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

lemma average_coordinate_memLp (m : ℕ) (g : X → ℝ) (hg : MemLp g 2 μ) :
    MemLp (fun x : Fin m → X => (∑ j, g (x j)) / m) 2 (sampleLaw μ m) := by
  have hs := (memLp_finset_sum Finset.univ (fun j _ => coordinate_memLp μ m g hg j)).const_smul
    (m : ℝ)⁻¹
  convert hs using 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Simultaneous empirical approximation of finitely many zero means.
The preliminary list may be arbitrarily long; no O(D) claim is made. -/
theorem exists_simultaneous_empirical_means {I : Type*} [Fintype I]
    (g : I → X → ℝ) (hg : ∀ i, Measurable (g i)) (hgp : ∀ i, MemLp (g i) 2 μ)
    (hzero : ∀ i, (∫ x, g i x ∂μ) = 0)
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ i x, |g i x| ≤ K)
    (ε : ℝ) (hε : 0 < ε) (minimum : ℕ) :
    ∃ m : ℕ, 0 < m ∧ minimum ≤ m ∧ ∃ ξ : Fin m → X,
      ∀ i, |(∑ j, g i (ξ j)) / m| < ε := by
  classical
  obtain ⟨n, hn⟩ := exists_nat_gt ((Fintype.card I : ℝ) * K ^ 2 / ε ^ 2)
  let m := n + minimum + 1
  have hm : 0 < m := by dsimp [m]; omega
  have hmin : minimum ≤ m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (n : ℝ) ≤ m := by exact_mod_cast (show n ≤ m by dsimp [m]; omega)
  have hsmall : ((Fintype.card I : ℝ) * K ^ 2) / m < ε ^ 2 := by
    apply (div_lt_iff₀ hmR).mpr
    have hh := (div_lt_iff₀ (sq_pos_of_pos hε)).mp (hn.trans_le hnR)
    nlinarith
  let total : (Fin m → X) → ℝ := fun x => ∑ i, ((∑ j, g i (x j)) / m) ^ 2
  have hi : ∀ i, Integrable (fun x : Fin m → X => ((∑ j, g i (x j)) / m) ^ 2)
      (sampleLaw μ m) := fun i => (average_coordinate_memLp μ m (g i) (hgp i)).integrable_sq
  have htotal : Integrable total (sampleLaw μ m) := integrable_finset_sum _ fun i _ => hi i
  have hmoment : ∀ i, (∫ x, g i x ^ 2 ∂μ) ≤ K ^ 2 := by
    intro i
    have hp : ∀ x, g i x ^ 2 ≤ K ^ 2 := fun x => by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (hbound i x)
    simpa using
      integral_mono (hgp i).integrable_sq (integrable_const (K ^ 2)) hp
  have hTI : (∫ x, total x ∂sampleLaw μ m) ≤ ((Fintype.card I : ℝ) * K ^ 2) / m := by
    rw [show (∫ x, total x ∂sampleLaw μ m) =
      ∑ i, (∫ x : Fin m → X, ((∑ j, g i (x j)) / m) ^ 2 ∂sampleLaw μ m) from
        integral_finset_sum _ (fun i _ => hi i)]
    simp_rw [integral_average_coordinate_sq μ m hm _ (hg _) (hgp _) (hzero _)]
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hmR.le
    exact (Finset.sum_le_sum (fun i _ => hmoment i)).trans_eq (by simp)
  have hex : ∃ ξ : Fin m → X, total ξ < ε ^ 2 := by
    by_contra! hnone
    have hcontra := integral_mono (integrable_const (ε ^ 2)) htotal hnone
    have hlower : ε ^ 2 ≤ ∫ x, total x ∂sampleLaw μ m := by simpa using hcontra
    linarith
  obtain ⟨ξ, hξ⟩ := hex
  refine ⟨m, hm, hmin, ξ, fun i => ?_⟩
  have hsingle := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) =>
    sq_nonneg ((∑ j, g l (ξ j)) / m)) (Finset.mem_univ i)
  have hs : ((∑ j, g i (ξ j)) / m) ^ 2 < ε ^ 2 := hsingle.trans_lt hξ
  exact (sq_lt_sq₀ (abs_nonneg _) hε.le).mp (by simpa only [sq_abs] using hs)

end Tusnady.LiteratureSampling
