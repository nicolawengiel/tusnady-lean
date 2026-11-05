import Tusnady.SparseMixedSampling
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Continuity on the actual open common dyadic cells. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators Topology
namespace Tusnady.SamplingSpace
open DyadicFunctions

lemma dyadicBoundary_isClosed (d H : ℕ) : IsClosed (dyadicBoundary d H) := by
  apply isClosed_iUnion_of_finite
  intro k
  apply isClosed_iUnion_of_finite
  intro i
  exact isClosed_eq (continuous_apply k) continuous_const

lemma samplingDomain_isOpen (d H : ℕ) : IsOpen (samplingDomain d H) := by
  have he : samplingDomain d H = {x | ∀ k, x k ∈ Ioo (0 : ℝ) 1} \ dyadicBoundary d H := by
    ext x
    constructor
    · rintro ⟨hx, hb⟩
      refine ⟨fun k => ⟨lt_of_le_of_ne (hx k).1 ?_, (hx k).2⟩, hb⟩
      intro he
      apply hb
      apply mem_iUnion.mpr ⟨k, ?_⟩
      apply mem_iUnion.mpr ⟨⟨0, Nat.succ_pos _⟩, ?_⟩
      simpa using he.symm
    · rintro ⟨hx, hb⟩
      exact ⟨fun k => ⟨(hx k).1.le, (hx k).2⟩, hb⟩
  rw [he]
  apply IsOpen.sdiff _ (dyadicBoundary_isClosed d H)
  simp only [Set.setOf_forall]
  exact isOpen_iInter_of_finite fun k => isOpen_Ioo.preimage (continuous_apply k)

lemma coordinate_open_cell (d H : ℕ) (x : samplingDomain d H) (k : Fin d) :
    ∃ i : Fin (2 ^ H), x.val k ∈ Ioo (dyadicLeft H i) (dyadicLeft H i + dyadicLength H) := by
  obtain ⟨i, hi, _⟩ := Haar.existsUnique_unit_interval H (x.val k) (x.property.1 k)
  refine ⟨i, ⟨lt_of_le_of_ne hi.1 ?_, hi.2⟩⟩
  intro he
  apply x.property.2
  apply mem_iUnion.mpr ⟨k, ?_⟩
  apply mem_iUnion.mpr ⟨⟨i.val, by omega⟩, ?_⟩
  simpa [dyadicLeft] using he.symm

lemma detailBasis_piecewiseAffine_of_le {j H : ℕ} (hj : j ≤ H)
    (i : Fin (Module.finrank ℝ (detailSpace j))) : PiecewiseAffine H (detailBasis j i) := by
  apply (mem_pointwiseSpace_iff H _).mp
  apply pointwiseSpace_mono hj
  exact ((mem_pointwiseSpace_iff j _).mpr (canonicalRepresentative_piecewiseAffine j _))

lemma detailBasis_continuousAt_coordinate {d H j : ℕ} (hj : j ≤ H)
    (i : Fin (Module.finrank ℝ (detailSpace j))) (x : samplingDomain d H) (k : Fin d) :
    ContinuousAt (detailBasis j i) (x.val k) := by
  obtain ⟨q, hq⟩ := coordinate_open_cell d H x k
  exact ((detailBasis_piecewiseAffine_of_le hj i).continuousOn_cell q).continuousAt
    (isOpen_Ioo.mem_nhds hq)

lemma sparseBasis_continuousOn (d H : ℕ) (i : SparseIndex d H) :
    ContinuousOn (sparseBasis d H i) (samplingDomain d H) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  change Filter.Tendsto (fun y : Fin d → ℝ => ∏ k, detailBasis (levelDepth i.1 k) (i.2 k) (y k))
    (𝓝 x) (𝓝 (∏ k, detailBasis (levelDepth i.1 k) (i.2 k) (x k)))
  apply tendsto_finset_prod
  intro k _
  have hk : levelDepth i.1 k ≤ H := by
    exact (Finset.single_le_sum (fun j _ => Nat.zero_le (levelDepth i.1 j))
      (Finset.mem_univ k)).trans i.1.property
  exact (detailBasis_continuousAt_coordinate hk (i.2 k) ⟨x, hx⟩ k).comp (f := fun y : Fin d → ℝ => y k)
    (continuous_apply k).continuousAt

lemma ambientBasis_continuousOn (d H : ℕ) (i : Fin (sparseDimension d H)) :
    ContinuousOn (ambientBasis d H i) (samplingDomain d H) :=
  sparseBasis_continuousOn d H _

lemma ambientBasis_restricted_continuous (d H : ℕ) (i : Fin (sparseDimension d H)) :
    Continuous (fun x : samplingDomain d H => ambientBasis d H i x) :=
  (continuousOn_iff_continuous_restrict.mp (ambientBasis_continuousOn d H i))

lemma samplingDomain_infinite_neighborhood (d H : ℕ) (hd : 0 < d)
    (x : samplingDomain d H) (s : Set (samplingDomain d H)) (hs : s ∈ 𝓝 x) : s.Infinite := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  haveI := Module.punctured_nhds_neBot ℝ (Fin d → ℝ) (x : Fin d → ℝ)
  have hn := (samplingDomain_isOpen d H).isOpenMap_subtype_val.image_mem_nhds hs
  have hi := infinite_of_mem_nhds (x : Fin d → ℝ) hn
  exact fun hf => hi (hf.image Subtype.val)

lemma continuous_zero_of_integral_sq_zero (d H : ℕ) (u : (Fin d → ℝ) → ℝ)
    (hu : MemLp u 2 (samplingAmbientMeasure d H))
    (huc : ContinuousOn u (samplingDomain d H))
    (hzero : (∫ x, u x ^ 2 ∂samplingAmbientMeasure d H) = 0) :
    ∀ x ∈ samplingDomain d H, u x = 0 := by
  have hi := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mp hu
  have ha := (integral_eq_zero_iff_of_nonneg_ae
    (Filter.Eventually.of_forall (fun x => sq_nonneg (u x))) hi).mp hzero
  have hae : u =ᵐ[samplingAmbientMeasure d H] 0 := by
    filter_upwards [ha] with x hx
    exact sq_eq_zero_iff.mp hx
  haveI : (productVolume d).IsOpenPosMeasure := by unfold productVolume; infer_instance
  exact Measure.eqOn_open_of_ae_eq hae (samplingDomain_isOpen d H) huc continuousOn_const

end Tusnady.SamplingSpace
