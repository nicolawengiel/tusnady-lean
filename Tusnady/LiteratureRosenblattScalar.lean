import Tusnady.Literature
import Tusnady.UniformMonomial
import Mathlib.Topology.Order.IntermediateValue

/-! # Scalar probability integral transform, proved for atomless laws -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
namespace Tusnady.LiteratureProof

theorem continuous_cdf_of_noAtoms (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    Continuous (cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hjump : ENNReal.ofReal (cdf μ x - Function.leftLim (cdf μ) x) = 0 := by
    rw [← StieltjesFunction.measure_singleton, measure_cdf μ, measure_singleton]
  have hle := ENNReal.ofReal_eq_zero.mp hjump
  have hleft : Function.leftLim (cdf μ) x = cdf μ x := by
    exact le_antisymm ((monotone_cdf μ).leftLim_le le_rfl) (by linarith)
  apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
  rw [hleft, (cdf μ).rightLim_eq]

theorem exists_cdf_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : ∃ x : ℝ, cdf μ x = t := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually_lt_const ht0).exists
  obtain ⟨b, hb⟩ := ((tendsto_cdf_atTop μ).eventually_const_lt ht1).exists
  exact intermediate_value_univ a b (continuous_cdf_of_noAtoms μ) ⟨ha.le, hb.le⟩

theorem cdf_sublevel_real (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ]
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) : μ.real {x | cdf μ x ≤ t} = t := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    let v := min (t + ε) ((t + 1) / 2)
    have htv : t < v := lt_min (by linarith) (by linarith)
    have hv0 : 0 < v := ht0.trans_lt htv
    have hv1 : v < 1 := (min_le_right _ _).trans_lt (by linarith)
    obtain ⟨a, ha⟩ := exists_cdf_eq μ hv0 hv1
    have hsub : {x | cdf μ x ≤ t} ⊆ Iic a := by
      intro x hx
      by_contra hxa
      have hax : a ≤ x := le_of_lt (lt_of_not_ge hxa)
      have hm := monotone_cdf μ hax
      change cdf μ x ≤ t at hx
      rw [ha] at hm
      exact (not_le.mpr htv) (hm.trans hx)
    calc
      _ ≤ μ.real (Iic a) := measureReal_mono hsub
      _ = v := (cdf_eq_real μ a).symm.trans ha
      _ ≤ t + ε := min_le_left _ _
  · by_cases ht : t = 0
    · rw [ht]
      exact measureReal_nonneg
    · obtain ⟨a, ha⟩ := exists_cdf_eq μ (lt_of_le_of_ne ht0 (Ne.symm ht)) ht1
      have hsub : Iic a ⊆ {x | cdf μ x ≤ t} := by
        intro x hx
        exact (monotone_cdf μ hx).trans_eq ha
      calc
        t = μ.real (Iic a) := ha.symm.trans (cdf_eq_real μ a)
        _ ≤ _ := measureReal_mono hsub

def uniformUnit : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance uniformUnit_probability : IsProbabilityMeasure uniformUnit := by
  constructor
  simp [uniformUnit, Real.volume_Icc]

theorem uniformUnit_Iic_middle {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    uniformUnit (Iic t) = ENNReal.ofReal t := by
  have hset : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans ht1⟩
  rw [uniformUnit, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc]
  simp

theorem cdf_map_uniformUnit (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    μ.map (cdf μ) = uniformUnit := by
  refine Measure.ext_of_Iic _ _ (fun t => ?_)
  rw [Measure.map_apply (monotone_cdf μ).measurable measurableSet_Iic]
  by_cases ht0 : t < 0
  · have hset : (cdf μ) ⁻¹' Iic t = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, notMem_empty, iff_false]
      exact not_le.mpr (ht0.trans_le (cdf_nonneg μ x))
    have hu : Iic t ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, notMem_empty, iff_false]
      rintro ⟨hx, hx0, _⟩
      linarith
    rw [hset, measure_empty, uniformUnit, Measure.restrict_apply measurableSet_Iic, hu, measure_empty]
  · have ht0' : 0 ≤ t := le_of_not_gt ht0
    by_cases ht1 : 1 ≤ t
    · have hset : (cdf μ) ⁻¹' Iic t = univ := by
        ext x
        simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
        exact (cdf_le_one μ x).trans ht1
      have hu : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
        apply inter_eq_right.mpr
        exact fun x hx => hx.2.trans ht1
      rw [hset, measure_univ, uniformUnit, Measure.restrict_apply measurableSet_Iic, hu,
        Real.volume_Icc]
      norm_num
    · rw [uniformUnit_Iic_middle ht0' (le_of_not_ge ht1)]
      have hreal := cdf_sublevel_real μ ht0' (lt_of_not_ge ht1)
      have hmeasure : μ ((cdf μ) ⁻¹' Iic t) = ENNReal.ofReal (μ.real {x | cdf μ x ≤ t}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top μ _)]
        rfl
      rw [hmeasure, hreal]

theorem uniformCentered_Iic_middle {t : ℝ} (_ht0 : -1 ≤ t) (ht1 : t ≤ 1) :
    UniformMonomial.scalarLaw (Iic t) = ENNReal.ofReal ((t + 1) / 2) := by
  have hset : Iic t ∩ Icc (-1 : ℝ) 1 = Icc (-1) t := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · exact fun h => ⟨h.2.1, h.1⟩
    · exact fun h => ⟨h.2, h.1, h.2.trans ht1⟩
  unfold UniformMonomial.scalarLaw ProbabilityTheory.cond
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iic, hset,
    Real.volume_Icc, Real.volume_Icc]
  norm_num
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num
  exact mul_comm _ _

theorem uniformUnit_affine_map :
    uniformUnit.map (fun x : ℝ => 2 * x - 1) = UniformMonomial.scalarLaw := by
  refine Measure.ext_of_Iic _ _ (fun t => ?_)
  rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
  have hpre : (fun x : ℝ => 2 * x - 1) ⁻¹' Iic t = Iic ((t + 1) / 2) := by
    ext x
    simp only [mem_preimage, mem_Iic]
    constructor <;> intro h <;> linarith
  rw [hpre]
  by_cases hlo : t < -1
  · have hU : uniformUnit (Iic ((t + 1) / 2)) = 0 := by
      rw [uniformUnit, Measure.restrict_apply measurableSet_Iic]
      have hset : Iic ((t + 1) / 2) ∩ Icc (0 : ℝ) 1 = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc, notMem_empty, iff_false]
        rintro ⟨hx, hx0, _⟩
        linarith
      rw [hset, measure_empty]
    have hC : UniformMonomial.scalarLaw (Iic t) = 0 := by
      unfold UniformMonomial.scalarLaw ProbabilityTheory.cond
      rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
      have hset : Iic t ∩ Icc (-1 : ℝ) 1 = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_Iic, mem_Icc, notMem_empty, iff_false]
        rintro ⟨hx, hx0, _⟩
        linarith
      rw [hset, measure_empty]
      simp
    rw [hU, hC]
  · have hlo' : -1 ≤ t := le_of_not_gt hlo
    by_cases hhi : 1 ≤ t
    · have hU : uniformUnit (Iic ((t + 1) / 2)) = 1 := by
        rw [uniformUnit, Measure.restrict_apply measurableSet_Iic]
        have hset : Iic ((t + 1) / 2) ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
          apply inter_eq_right.mpr
          intro x hx
          change x ≤ (t + 1) / 2
          linarith [hx.2]
        rw [hset, Real.volume_Icc]
        norm_num
      have hC : UniformMonomial.scalarLaw (Iic t) = 1 := by
        unfold UniformMonomial.scalarLaw ProbabilityTheory.cond
        rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
        have hset : Iic t ∩ Icc (-1 : ℝ) 1 = Icc (-1) 1 :=
          inter_eq_right.mpr (fun _ hx => hx.2.trans hhi)
        rw [hset, Real.volume_Icc]
        norm_num
        exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
      rw [hU, hC]
    · rw [uniformUnit_Iic_middle (by linarith) (by linarith),
        uniformCentered_Iic_middle hlo' (le_of_not_ge hhi)]

theorem normalized_cdf_map_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ] [NoAtoms μ] :
    μ.map (fun x => 2 * cdf μ x - 1) =
      ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1 : ℝ) 1) := by
  calc
    _ = (μ.map (cdf μ)).map (fun x : ℝ => 2 * x - 1) :=
      (Measure.map_map (by fun_prop) (monotone_cdf μ).measurable).symm
    _ = _ := by rw [cdf_map_uniformUnit, uniformUnit_affine_map]; rfl

end Tusnady.LiteratureProof
