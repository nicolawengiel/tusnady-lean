import Tusnady.SamplingSpaceCounting

/-!
# The actual open-cell sampling domain and its measure

The domain is the unit cube with all depth-H dyadic coordinate grid
hyperplanes removed. Its measure is constructed by comap of product
Lebesgue measure. It is a genuine probability measure; integrals of the
actual supported sampling functions are transferred without a free
full-measure or orthonormality hypothesis.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

def unitCube (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ k, x k ∈ Ico (0 : ℝ) 1}

def dyadicBoundary (d H : ℕ) : Set (Fin d → ℝ) :=
  ⋃ k : Fin d, ⋃ i : Fin (2 ^ H + 1), {x | x k = (i.val : ℝ) / (2 : ℝ) ^ H}

def samplingDomain (d H : ℕ) : Set (Fin d → ℝ) := unitCube d \ dyadicBoundary d H

lemma unitCube_measurable (d : ℕ) : MeasurableSet (unitCube d) := by
  simp only [unitCube, Set.setOf_forall]
  exact MeasurableSet.iInter fun k => (measurable_pi_apply k) measurableSet_Ico

lemma unitCube_volume (d : ℕ) : productVolume d (unitCube d) = 1 := by
  have heq : unitCube d = Set.pi Set.univ (fun _ : Fin d => Ico (0 : ℝ) 1) := by
    ext x
    simp [unitCube]
  rw [heq]
  unfold productVolume
  rw [Measure.pi_pi]
  simp [Real.volume_Ico]

lemma dyadicBoundary_measurable (d H : ℕ) : MeasurableSet (dyadicBoundary d H) := by
  apply MeasurableSet.iUnion
  intro k
  apply MeasurableSet.iUnion
  intro i
  exact measurableSet_eq_fun (measurable_pi_apply k) measurable_const

lemma dyadicBoundary_volume_zero (d H : ℕ) : productVolume d (dyadicBoundary d H) = 0 := by
  apply measure_iUnion_null
  intro k
  apply measure_iUnion_null
  intro i
  exact Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure ℝ)) k _

lemma samplingDomain_measurable (d H : ℕ) : MeasurableSet (samplingDomain d H) :=
  (unitCube_measurable d).diff (dyadicBoundary_measurable d H)

lemma samplingDomain_ae_cube (d H : ℕ) :
    samplingDomain d H =ᵐ[productVolume d] unitCube d := by
  have hn : ∀ᵐ x ∂productVolume d, x ∉ dyadicBoundary d H := by
    rw [ae_iff]
    simpa using dyadicBoundary_volume_zero d H
  filter_upwards [hn] with x hx
  apply propext
  change (x ∈ unitCube d ∧ x ∉ dyadicBoundary d H) ↔ x ∈ unitCube d
  exact ⟨And.left, fun h => ⟨h, hx⟩⟩

lemma samplingDomain_volume (d H : ℕ) : productVolume d (samplingDomain d H) = 1 := by
  rw [measure_congr (samplingDomain_ae_cube d H), unitCube_volume]

lemma samplingDomain_nonempty (d H : ℕ) : (samplingDomain d H).Nonempty := by
  by_contra h
  have he := Set.not_nonempty_iff_eq_empty.mp h
  have hm := samplingDomain_volume d H
  simp [he] at hm

def samplingMeasure (d H : ℕ) : Measure (samplingDomain d H) :=
  (productVolume d).comap Subtype.val

instance samplingMeasure_isProbability (d H : ℕ) : IsProbabilityMeasure (samplingMeasure d H) := by
  constructor
  rw [samplingMeasure, comap_subtype_coe_apply (samplingDomain_measurable d H)]
  simpa using samplingDomain_volume d H

lemma detailBasis_zero_outside (j : ℕ) (i : Fin (Module.finrank ℝ (detailSpace j)))
    (x : ℝ) (hx : x ∉ Ico (0 : ℝ) 1) : detailBasis j i x = 0 :=
  pointwiseSynthesis_zero_outside j _ x hx

lemma tensorBasis_zero_outside {d : ℕ} (ℓ : Fin d → ℕ) (i : TensorIndex ℓ)
    (x : Fin d → ℝ) (hx : x ∉ unitCube d) : tensorBasis ℓ i x = 0 := by
  classical
  have hnot : ¬ ∀ k, x k ∈ Ico (0 : ℝ) 1 := hx
  obtain ⟨k, hk⟩ := not_forall.mp hnot
  exact Finset.prod_eq_zero (Finset.mem_univ k) (detailBasis_zero_outside _ _ _ hk)

lemma sparseBasis_zero_outside (d H : ℕ) (i : SparseIndex d H) (x : Fin d → ℝ)
    (hx : x ∉ unitCube d) : sparseBasis d H i x = 0 :=
  tensorBasis_zero_outside _ _ x hx

/-- Actual integral transfer from the open-cell domain back to global
Lebesgue measure for any function supported on the unit cube. -/
theorem samplingMeasure_integral (d H : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : ∀ x, x ∉ unitCube d → f x = 0) :
    (∫ x : samplingDomain d H, f x ∂samplingMeasure d H) = ∫ x, f x ∂productVolume d := by
  rw [samplingMeasure, integral_subtype_comap (samplingDomain_measurable d H)]
  rw [Measure.restrict_congr_set (samplingDomain_ae_cube d H)]
  rw [← integral_indicator (unitCube_measurable d)]
  congr 1
  funext x
  by_cases hx : x ∈ unitCube d <;> simp [hx, hf x]

end Tusnady.SamplingSpace
