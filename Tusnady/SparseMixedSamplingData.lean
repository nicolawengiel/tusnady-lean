import Tusnady.SparseSamplingExtension

/-!
# Actual measure and density data of the proved one-function extension

Every field used here comes from construct_augmented_data. The good domain
and all normalization/change-of-measure statements are real measure objects.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal ENNReal
namespace Tusnady.SamplingSpace
namespace AugmentedData
variable {d H : ℕ} {u : (Fin d → ℝ) → ℝ}

def measure (A : AugmentedData d H u) : Measure A.domain :=
  (productVolume d).comap Subtype.val

instance measure_isProbability (A : AugmentedData d H u) : IsProbabilityMeasure A.measure :=
  refinedMeasure_isProbability d H A.domain A.measurable_domain A.domain_ae

def restrictedBasis (A : AugmentedData d H u) (i : Fin A.dimension) (x : A.domain) : ℝ :=
  A.basis i x

lemma restrictedBasis_measurable (A : AugmentedData d H u) (i : Fin A.dimension) :
    Measurable (A.restrictedBasis i) := (A.basis_measurable i).comp measurable_subtype_coe

lemma restrictedBasis_memLp (A : AugmentedData d H u) (i : Fin A.dimension) :
    MemLp (A.restrictedBasis i) 2 A.measure := by
  have hmap : A.measure.map ((↑) : A.domain → Fin d → ℝ) = samplingAmbientMeasure d H := by
    rw [measure, map_comap_subtype_coe A.measurable_domain, Measure.restrict_congr_set A.domain_ae]
    rfl
  have h := A.basis_memLp i
  rw [← hmap] at h
  exact (MeasurableEmbedding.subtype_coe A.measurable_domain).memLp_map_measure_iff.mp h

lemma restrictedBasis_product_integrable (A : AugmentedData d H u) (i j : Fin A.dimension) :
    Integrable (fun x => A.restrictedBasis i x * A.restrictedBasis j x) A.measure :=
  (A.restrictedBasis_memLp i).integrable_mul (A.restrictedBasis_memLp j)

lemma restrictedBasis_inner (A : AugmentedData d H u) (i j : Fin A.dimension) :
    (∫ x, A.restrictedBasis i x * A.restrictedBasis j x ∂A.measure) = if i = j then 1 else 0 := by
  have ht := refinedMeasure_integral d H A.domain A.measurable_domain A.domain_ae
    (fun x => A.basis i x * A.basis j x)
  exact ht.trans (A.basis_inner i j)

def density (A : AugmentedData d H u) (x : A.domain) : ℝ≥0 :=
  ⟨(1 / (A.dimension : ℝ)) * ∑ i, A.restrictedBasis i x ^ 2, by positivity⟩

lemma density_formula (A : AugmentedData d H u) (x : A.domain) :
    (A.density x : ℝ) = (1 / (A.dimension : ℝ)) * ∑ i, A.restrictedBasis i x ^ 2 := rfl

lemma density_measurable (A : AugmentedData d H u) : Measurable A.density := by
  apply Measurable.subtype_mk
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (A.restrictedBasis_measurable i).pow_const 2)

/-- Adding at most one actual basis vector reduces the already proved
uniform density lower bound by at most two. -/
theorem density_lower (A : AugmentedData d H u) (hd : 0 < d) (x : A.domain) :
    (((1 : ℝ) / 28) ^ d / 2) ≤ (A.density x : ℝ) := by
  have hb : 1 ≤ sparseDimension d H := sparseDimension_pos d H hd
  have hD : (0 : ℝ) < A.dimension := by exact_mod_cast A.dimension_pos
  have hdim : (A.dimension : ℝ) ≤ 2 * (sparseDimension d H : ℝ) := by
    have hupper : (A.dimension : ℝ) ≤ sparseDimension d H + 1 := by exact_mod_cast A.dimension_upper
    have hb' : (1 : ℝ) ≤ sparseDimension d H := by exact_mod_cast hb
    nlinarith
  rw [density_formula]
  have hsum := A.square_sum_lower x x.property
  have hprod : ((((1 : ℝ) / 28) ^ d / 2) * A.dimension) ≤
      ((1 : ℝ) / 28) ^ d * sparseDimension d H := by
    calc
      _ ≤ (((1 : ℝ) / 28) ^ d / 2) * (2 * sparseDimension d H) :=
        mul_le_mul_of_nonneg_left hdim (by positivity)
      _ = _ := by ring
  have hdiv := (le_div_iff₀ hD).mpr (hprod.trans hsum)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one, restrictedBasis] using hdiv

lemma density_positive (A : AugmentedData d H u) (hd : 0 < d) : ∀ x, 0 < A.density x := by
  intro x
  exact_mod_cast lt_of_lt_of_le (by positivity : (0 : ℝ) < ((1 : ℝ) / 28) ^ d / 2) (A.density_lower hd x)

lemma integral_transfer (A : AugmentedData d H u) (f : (Fin d → ℝ) → ℝ) :
    (∫ x : A.domain, f x ∂A.measure) = ∫ x, f x ∂samplingAmbientMeasure d H :=
  refinedMeasure_integral d H A.domain A.measurable_domain A.domain_ae f

end AugmentedData
end Tusnady.SamplingSpace
