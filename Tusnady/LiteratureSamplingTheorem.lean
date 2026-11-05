import Tusnady.LiteratureSamplingReindex
import Tusnady.FrameLTSelection

/-! # Unconditional proof of the exact t=1 sampling input

The preliminary sample, MSS frame partition, LT subset iteration and
finite reindexing are all proved. This theorem has exactly the original
literature target type, with universal constants independent of dimension.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.LiteratureProof

/-- Complete proof of the exact unweighted t=1 sampling input. -/
theorem sampling : Literature.Sampling := by
  refine ⟨Frame.selectionConstant, 25 / Frame.selectionConstant, Frame.selectionConstant,
    Frame.selectionConstant_pos, div_pos (by norm_num) Frame.selectionConstant_pos,
    Frame.selectionConstant_pos, ?_⟩
  intro ambient D hD Ω _hΩ μ hμ u humeas hint horth hE
  letI : IsProbabilityMeasure μ := hμ
  obtain ⟨M,hM,hmin,ξ,hnorm,henergy⟩ :=
    LiteratureSampling.exists_finite_frame_approximation μ u hD humeas hint horth hE (201*D)
  obtain ⟨S,hcardlow,hcardup,hS⟩ :=
    Frame.exists_small_subset (LiteratureSampling.nodeVector u ξ) hD hM hmin hnorm henergy
  refine ⟨S.card, hD.trans_le hcardlow, hcardup,
    fun j => ξ (LiteratureSampling.selectedIndex S j), ?_⟩
  intro a
  have hh := LiteratureSampling.selected_average_bounds u ξ hD hM S Frame.selectionConstant
    Frame.selectionConstant_pos hcardlow hcardup hS a
  rwa [LiteratureSampling.integral_combination_abs_sq μ u humeas horth hE a]

end Tusnady.LiteratureProof
