import Tusnady.Upper.Ehrhard.GaussianSections
import Tusnady.Upper.Ehrhard.ConvexConcavity

/-!
# Gaussian Ehrhard symmetrization with finite CDF values

The definition `Φ(last z) ≤ sectionMass(front z)` handles zero and full section
mass directly.  Gaussian mass preservation is proved by the actual Fubini
formula.  Convexity for compact convex inputs follows from the proved partial
Gaussian CDF concavity theorem; there is no extra Gaussian or fold hypothesis.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal RealInnerProductSpace

namespace OAI.GaussianPropeller.Symmetrization
open Quantile GaussianSections EhrhardSmooth

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))

def sectionMass (K : Set E') (y : E) : ℝ := (gaussianReal 0 1).real (verticalSection K y)

def symmetrization (K : Set E') : Set E' := {z | Φ (last z) ≤ sectionMass K (front z)}

theorem cdf_eq_gaussianReal (a : ℝ) : Φ a = (gaussianReal 0 1).real (Iic a) := by
  rw [measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))]
  unfold Φ
  congr 1
  funext x
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, φ]

theorem gaussian_cdf_sublevel_mass (p : ℝ) (hp : p ∈ Icc (0 : ℝ) 1) :
    (gaussianReal 0 1).real {t | Φ t ≤ p} = p := by
  by_cases hz : p = 0
  · subst p
    have heq : {t : ℝ | Φ t ≤ 0} = ∅ := by ext t; simp [(Φ_pos t).not_ge]
    simp [heq]
  by_cases ho : p = 1
  · subst p
    have heq : {t : ℝ | Φ t ≤ 1} = univ := by ext t; simp [(Φ_lt_one t).le]
    simp [heq]
  have hp' : p ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hp.1 (Ne.symm hz), lt_of_le_of_ne hp.2 ho⟩
  have heq : {t : ℝ | Φ t ≤ p} = Iic (q p) := by
    ext t
    change Φ t ≤ p ↔ t ≤ q p
    simpa only [Φ_q hp'] using
      (strictMono_Φ.le_iff_le : Φ t ≤ Φ (q p) ↔ t ≤ q p)
  rw [heq, ← cdf_eq_gaussianReal, Φ_q hp']

theorem sectionMass_mem (K : Set E') (y : E) : sectionMass K y ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact measureReal_nonneg
  · simpa only [sectionMass, probReal_univ] using
      measureReal_mono (μ := gaussianReal 0 1) (subset_univ (verticalSection K y))

theorem measurable_sectionMass {K : Set E'} (hK : MeasurableSet K) : Measurable (sectionMass K) :=
  (measurable_verticalSection_mass hK).ennreal_toReal

theorem measurableSet_symmetrization {K : Set E'} (hK : MeasurableSet K) :
    MeasurableSet (symmetrization K) :=
  measurableSet_le (continuous_Φ.comp continuous_last).measurable
    ((measurable_sectionMass hK).comp continuous_front.measurable)

theorem verticalSection_symmetrization (K : Set E') (y : E) :
    verticalSection (symmetrization K) y = {t | Φ t ≤ sectionMass K y} := by
  ext t
  simp only [verticalSection, mem_setOf_eq, symmetrization, append_last, front_append]

/-- The symmetrization preserves the actual Gaussian measure, also for zero or
full fibers. -/
theorem gaussian_mass_symmetrization (K : Set E') (hK : MeasurableSet K) :
    (gaussianMeasure (Fin (k + 1))).real (symmetrization K) =
      (gaussianMeasure (Fin (k + 1))).real K := by
  rw [gaussianMeasure_real_sections _ (measurableSet_symmetrization hK),
    gaussianMeasure_real_sections _ hK]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    rw [verticalSection_symmetrization]
    exact gaussian_cdf_sublevel_mass _ (sectionMass_mem K y))

theorem sectionMass_lt_one_of_compact (K : Set E') (hK : IsCompact K) (y : E) :
    sectionMass K y < 1 := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hs : verticalSection K y ⊆ Iic R := by
    intro t ht
    have hc : |t| ≤ ‖append y t‖ := by
      simpa only [Real.norm_eq_abs, show append y t (Fin.last k) = t from append_last y t] using
        PiLp.norm_apply_le (append y t) (Fin.last k)
    exact (le_abs_self t).trans (hc.trans (hR _ ht))
  exact (measureReal_mono (μ := gaussianReal 0 1) hs).trans_lt
    (by rw [← cdf_eq_gaussianReal]; exact Φ_lt_one R)

private def keepVertical (i : Fin (k + 1)) : Bool := decide (i = Fin.last k)

private theorem last_law : (gaussianMeasure (Fin (k + 1))).map (last : E' → ℝ) =
    gaussianReal 0 1 := by
  have h := (measurePreserving_snd (μ := gaussianMeasure (Fin k))
    (ν := gaussianReal 0 1)).comp (split_measurePreserving (k := k))
  exact h.map_eq

private theorem append_zero_add_projection (y : E) (z : E') :
    append y 0 + CoordinateProjection.projection keepVertical z = append y (last z) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [append, last, CoordinateProjection.projection_apply, keepVertical]
  · simp [append, CoordinateProjection.projection_apply, keepVertical, Fin.castSucc_ne_last]

private theorem sectionProbability_vertical (K : Set E') (hK : MeasurableSet K) (y : E) :
    sectionProbability K (CoordinateProjection.projection keepVertical) (append y 0) =
      sectionMass K y := by
  unfold sectionProbability sectionMass
  rw [← last_law, map_measureReal_apply continuous_last.measurable
    (measurableSet_verticalSection hK y)]
  congr 1
  ext z
  change append y 0 + CoordinateProjection.projection keepVertical z ∈ K ↔ append y (last z) ∈ K
  rw [append_zero_add_projection]

private theorem append_linear_combination (x y : E) (s t a b : ℝ) :
    a • append x s + b • append y t = append (a • x + b • y) (a * s + b * t) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [append, smul_eq_mul]

/-- Genuine convexity of Gaussian symmetrization for compact convex inputs,
proved through the actual partial Gaussian section theorem. -/
theorem convex_symmetrization (K : Set E') (hKcomp : IsCompact K) (hKconv : Convex ℝ K) :
    Convex ℝ (symmetrization K) := by
  intro x hx y hy a b ha hb hab
  have hpx : sectionMass K (front x) ∈ Ioo (0 : ℝ) 1 :=
    ⟨(Φ_pos (last x)).trans_le hx, sectionMass_lt_one_of_compact K hKcomp _⟩
  have hpy : sectionMass K (front y) ∈ Ioo (0 : ℝ) 1 :=
    ⟨(Φ_pos (last y)).trans_le hy, sectionMass_lt_one_of_compact K hKcomp _⟩
  have hsx : last x ≤ q (sectionMass K (front x)) := by
    apply strictMono_Φ.le_iff_le.mp
    rw [Φ_q hpx]
    exact hx
  have hsy : last y ≤ q (sectionMass K (front y)) := by
    apply strictMono_Φ.le_iff_le.mp
    rw [Φ_q hpy]
    exact hy
  have hcdf := closedConvexProbability_projection_cdf_concavity K hKcomp.isClosed hKconv
    keepVertical (append (front x) 0) (append (front y) 0) ha hb hab
    (by simpa only [sectionProbability_vertical K hKcomp.isClosed.measurableSet] using hpx)
    (by simpa only [sectionProbability_vertical K hKcomp.isClosed.measurableSet] using hpy)
  rw [append_linear_combination] at hcdf
  simp only [mul_zero, add_zero, sectionProbability_vertical K hKcomp.isClosed.measurableSet] at hcdf
  have hfront : front (a • x + b • y) = a • front x + b • front y := by ext i; simp [front]
  have hlast : last (a • x + b • y) = a * last x + b * last y := by simp [last, smul_eq_mul]
  change Φ (last (a • x + b • y)) ≤ sectionMass K (front (a • x + b • y))
  rw [hfront, hlast]
  apply le_trans _ hcdf
  apply strictMono_Φ.monotone
  exact add_le_add (mul_le_mul_of_nonneg_left hsx ha) (mul_le_mul_of_nonneg_left hsy hb)

end OAI.GaussianPropeller.Symmetrization
