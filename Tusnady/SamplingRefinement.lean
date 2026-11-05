import Tusnady.SamplingDomainBasis

/-!
# Genuine full-measure domain refinement

A measurable additional identity valid almost everywhere can be made
pointwise by intersecting Ω with its actual truth set. The new measure,
probability normalization and integral transfer are all constructed.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

def samplingAmbientMeasure (d H : ℕ) : Measure (Fin d → ℝ) :=
  (productVolume d).restrict (samplingDomain d H)

instance samplingAmbientMeasure_isProbability (d H : ℕ) :
    IsProbabilityMeasure (samplingAmbientMeasure d H) := by
  constructor
  simpa [samplingAmbientMeasure] using samplingDomain_volume d H

def ambientBasis (d H : ℕ) (i : Fin (sparseDimension d H)) : (Fin d → ℝ) → ℝ :=
  sparseBasis d H (sparseEnumeration d H i)

lemma ambientBasis_measurable (d H : ℕ) (i : Fin (sparseDimension d H)) :
    Measurable (ambientBasis d H i) := sparseBasis_measurable d H _

lemma ambientBasis_memLp (d H : ℕ) (i : Fin (sparseDimension d H)) :
    MemLp (ambientBasis d H i) 2 (samplingAmbientMeasure d H) :=
  (sparseBasis_memLp d H _).restrict _

lemma ambientBasis_inner (d H : ℕ) (i j : Fin (sparseDimension d H)) :
    (∫ x, ambientBasis d H i x * ambientBasis d H j x ∂samplingAmbientMeasure d H) =
      if i = j then 1 else 0 := by
  rw [samplingAmbientMeasure, ← integral_subtype_comap (samplingDomain_measurable d H)]
  exact domainBasis_inner d H i j

lemma ambientBasis_square_sum (d H : ℕ) (x : Fin d → ℝ) :
    (∑ i, ambientBasis d H i x ^ 2) = sparseChristoffel d H x :=
  (sparseEnumeration d H).sum_comp (fun i => sparseBasis d H i x ^ 2)

def refinedDomain (d H : ℕ) (r : (Fin d → ℝ) → ℝ) : Set (Fin d → ℝ) :=
  samplingDomain d H ∩ {x | r x = 0}

lemma refinedDomain_measurable (d H : ℕ) (r : (Fin d → ℝ) → ℝ) (hr : Measurable r) :
    MeasurableSet (refinedDomain d H r) :=
  (samplingDomain_measurable d H).inter (measurableSet_eq_fun hr measurable_const)

lemma refinedDomain_ae (d H : ℕ) (r : (Fin d → ℝ) → ℝ)
    (hr : r =ᵐ[samplingAmbientMeasure d H] 0) :
    refinedDomain d H r =ᵐ[productVolume d] samplingDomain d H := by
  have hi : ∀ᵐ x ∂productVolume d, x ∈ samplingDomain d H → r x = 0 :=
    ae_imp_of_ae_restrict hr
  filter_upwards [hi] with x hx
  apply propext
  change (x ∈ samplingDomain d H ∧ r x = 0) ↔ x ∈ samplingDomain d H
  exact ⟨And.left, fun h => ⟨h, hx h⟩⟩

/-- Every measurable refinement equal to Ω almost everywhere carries a
constructed comap probability measure. -/
theorem refinedMeasure_isProbability (d H : ℕ) (S : Set (Fin d → ℝ))
    (hS : MeasurableSet S) (hAE : S =ᵐ[productVolume d] samplingDomain d H) :
    IsProbabilityMeasure ((productVolume d).comap ((↑) : S → Fin d → ℝ)) := by
  constructor
  rw [comap_subtype_coe_apply hS]
  have hm : productVolume d S = 1 := by rw [measure_congr hAE, samplingDomain_volume]
  simpa using hm

theorem refinedMeasure_integral (d H : ℕ) (S : Set (Fin d → ℝ))
    (hS : MeasurableSet S) (hAE : S =ᵐ[productVolume d] samplingDomain d H)
    (f : (Fin d → ℝ) → ℝ) :
    (∫ x : S, f x ∂(productVolume d).comap Subtype.val) =
      ∫ x, f x ∂samplingAmbientMeasure d H := by
  rw [integral_subtype_comap hS, Measure.restrict_congr_set hAE]
  rfl

lemma refinedDomain_nonempty (d H : ℕ) (S : Set (Fin d → ℝ))
    (hAE : S =ᵐ[productVolume d] samplingDomain d H) : S.Nonempty := by
  have hm : productVolume d S = 1 := by rw [measure_congr hAE, samplingDomain_volume]
  by_contra h
  have he := Set.not_nonempty_iff_eq_empty.mp h
  simp [he] at hm

end Tusnady.SamplingSpace
