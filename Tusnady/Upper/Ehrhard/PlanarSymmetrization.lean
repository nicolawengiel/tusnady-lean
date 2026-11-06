import Tusnady.Upper.Ehrhard.SymmetrizationClosed
import Tusnady.Upper.Ehrhard.CoordinateSections
import Tusnady.Upper.Ehrhard.GaussianBallAsymptotics

/-!
# The second Ehrhard symmetrization, into the plane

The horizontal section probability is taken under the actual finite product
Gaussian.  The planar set uses the finite CDF inequality, so zero and full
section masses are handled without infinite quantiles.  Mass preservation and
the convexity implication are proved here.  For the first symmetrization of a
compact input the required strict upper mass bound follows from compactness
of every horizontal section, in every positive horizontal dimension.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace OAI.GaussianPropeller.PlanarSymmetrization
open Quantile GaussianSections EhrhardSmooth Symmetrization

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

def horizontalSection (K : Set E') (t : ℝ) : Set E := {y | append y t ∈ K}
def horizontalMass (K : Set E') (t : ℝ) : ℝ := (gaussianMeasure (Fin k)).real (horizontalSection K t)
def planarSymmetrization (K : Set E') : Set Plane := {z | Φ (z 0) ≤ horizontalMass K (z 1)}

theorem measurableSet_horizontalSection {K : Set E'} (hK : MeasurableSet K) (t : ℝ) :
    MeasurableSet (horizontalSection K t) :=
  hK.preimage (continuous_append.comp (continuous_id.prodMk continuous_const)).measurable

theorem isClosed_horizontalSection {K : Set E'} (hK : IsClosed K) (t : ℝ) :
    IsClosed (horizontalSection K t) :=
  hK.preimage (continuous_append.comp (continuous_id.prodMk continuous_const))

theorem measurable_horizontalMass {K : Set E'} (hK : MeasurableSet K) : Measurable (horizontalMass K) :=
  (measurable_measure_prodMk_right (hK.preimage continuous_append.measurable)).ennreal_toReal

theorem horizontalMass_mem (K : Set E') (t : ℝ) : horizontalMass K t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact measureReal_nonneg
  · simpa only [horizontalMass, probReal_univ] using
      measureReal_mono (μ := gaussianMeasure (Fin k)) (subset_univ (horizontalSection K t))

theorem gaussianMeasure_horizontal_sections (K : Set E') (hK : MeasurableSet K) :
    (gaussianMeasure (Fin (k + 1))) K =
      ∫⁻ t, (gaussianMeasure (Fin k)) (horizontalSection K t) ∂gaussianReal 0 1 := by
  have hpre : MeasurableSet ((fun p : E × ℝ => append p.1 p.2) ⁻¹' K) :=
    hK.preimage continuous_append.measurable
  calc
    (gaussianMeasure (Fin (k + 1))) K =
        ((gaussianMeasure (Fin (k + 1))).map (split : E' → E × ℝ))
          ((fun p : E × ℝ => append p.1 p.2) ⁻¹' K) := by
      rw [Measure.map_apply continuous_split.measurable hpre]
      congr 1
      ext z
      simp [split]
    _ = ((gaussianMeasure (Fin k)).prod (gaussianReal 0 1))
        ((fun p : E × ℝ => append p.1 p.2) ⁻¹' K) := by rw [split_law]
    _ = _ := by rw [Measure.prod_apply_symm hpre]; rfl

theorem gaussianMeasure_real_horizontal_sections (K : Set E') (hK : MeasurableSet K) :
    (gaussianMeasure (Fin (k + 1))).real K =
      ∫ t, horizontalMass K t ∂gaussianReal 0 1 := by
  rw [measureReal_def, gaussianMeasure_horizontal_sections K hK]
  symm
  exact integral_toReal
    (measurable_measure_prodMk_right (hK.preimage continuous_append.measurable)).aemeasurable
    (ae_of_all _ (fun _ => measure_lt_top _ _))

theorem measurableSet_planarSymmetrization {K : Set E'} (hK : MeasurableSet K) :
    MeasurableSet (planarSymmetrization K) :=
  measurableSet_le (continuous_Φ.comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0)).measurable
    ((measurable_horizontalMass hK).comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).measurable)

private theorem coordinate_one_law :
    (gaussianMeasure (Fin 1)).map (fun x : EuclideanSpace ℝ (Fin 1) => x 0) = gaussianReal 0 1 := by
  exact (measurePreserving_snd.comp (split_measurePreserving (k := 0))).map_eq

theorem horizontalMass_planarSymmetrization (K : Set E') (t : ℝ) :
    horizontalMass (planarSymmetrization K) t = horizontalMass K t := by
  have hsub : horizontalSection (planarSymmetrization K) t =
      (fun x : EuclideanSpace ℝ (Fin 1) => x 0) ⁻¹' {s | Φ s ≤ horizontalMass K t} := by
    ext x
    change Φ (append x t (0 : Fin 1).castSucc) ≤ horizontalMass K (last (append x t)) ↔
      Φ (x 0) ≤ horizontalMass K t
    rw [append_castSucc, append_last]
  unfold horizontalMass
  rw [hsub, ← map_measureReal_apply (by fun_prop)
    (measurableSet_le continuous_Φ.measurable measurable_const), coordinate_one_law]
  exact gaussian_cdf_sublevel_mass _ (horizontalMass_mem K t)

/-- The planar reduction preserves exactly the actual Gaussian mass. -/
theorem gaussian_mass_planarSymmetrization (K : Set E') (hK : MeasurableSet K) :
    (gaussianMeasure (Fin 2)).real (planarSymmetrization K) =
      (gaussianMeasure (Fin (k + 1))).real K := by
  rw [gaussianMeasure_real_horizontal_sections _ (measurableSet_planarSymmetrization hK),
    gaussianMeasure_real_horizontal_sections _ hK]
  exact integral_congr_ae (ae_of_all _ (horizontalMass_planarSymmetrization K))

theorem sectionProbability_horizontal (K : Set E') (hK : MeasurableSet K) (t : ℝ) :
    sectionProbability K (CoordinateProjection.projection keepFront) (append (0 : E) t) =
      horizontalMass K t := by
  let B : Set (E × ℝ) := (fun p => append p.1 p.2) ⁻¹' K
  have hB : MeasurableSet B := hK.preimage continuous_append.measurable
  have heq : splitEquiv ⁻¹' B = K := by
    ext z
    simp only [B, mem_preimage]
    change append (front z) (last z) ∈ K ↔ z ∈ K
    rw [append_front_last]
  have h := sectionProbability_front B hB t
  rw [heq] at h
  exact h

/-- The strict upper mass condition is geometric, and is proved below for the
actual symmetrized compact inputs.  No analytic inequality is assumed. -/
theorem convex_planarSymmetrization (K : Set E') (hKclosed : IsClosed K) (hKconv : Convex ℝ K)
    (hupper : ∀ t, horizontalMass K t < 1) : Convex ℝ (planarSymmetrization K) := by
  intro x hx y hy a b ha hb hab
  have hpx : horizontalMass K (x 1) ∈ Ioo (0 : ℝ) 1 :=
    ⟨(Φ_pos (x 0)).trans_le hx, hupper _⟩
  have hpy : horizontalMass K (y 1) ∈ Ioo (0 : ℝ) 1 :=
    ⟨(Φ_pos (y 0)).trans_le hy, hupper _⟩
  have hsx : x 0 ≤ q (horizontalMass K (x 1)) := by
    apply strictMono_Φ.le_iff_le.mp
    rw [Φ_q hpx]
    exact hx
  have hsy : y 0 ≤ q (horizontalMass K (y 1)) := by
    apply strictMono_Φ.le_iff_le.mp
    rw [Φ_q hpy]
    exact hy
  have hcdf := closedConvexProbability_projection_cdf_concavity K hKclosed hKconv keepFront
    (append (0 : E) (x 1)) (append (0 : E) (y 1)) ha hb hab
    (by simpa only [sectionProbability_horizontal K hKclosed.measurableSet] using hpx)
    (by simpa only [sectionProbability_horizontal K hKclosed.measurableSet] using hpy)
  have heq : a • append (0 : E) (x 1) + b • append (0 : E) (y 1) =
      append (0 : E) (a * x 1 + b * y 1) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [append, smul_eq_mul]
  rw [heq] at hcdf
  simp only [sectionProbability_horizontal K hKclosed.measurableSet] at hcdf
  change Φ ((a • x + b • y) 0) ≤ horizontalMass K ((a • x + b • y) 1)
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  apply le_trans _ hcdf
  exact strictMono_Φ.monotone
    (add_le_add (mul_le_mul_of_nonneg_left hsx ha) (mul_le_mul_of_nonneg_left hsy hb))

theorem horizontalSection_symmetrization_subset (K : Set E') (t : ℝ) :
    horizontalSection (symmetrization K) t ⊆ front '' K := by
  intro y hy
  have hp : 0 < sectionMass K y := (Φ_pos t).trans_le (by simpa [horizontalSection, symmetrization] using hy)
  obtain ⟨s, hs⟩ := nonempty_of_measureReal_ne_zero hp.ne'
  exact ⟨append y s, hs, front_append y s⟩

theorem isCompact_horizontalSection_symmetrization (K : Set E') (hKcomp : IsCompact K) (t : ℝ) :
    IsCompact (horizontalSection (symmetrization K) t) :=
  (hKcomp.image continuous_front).of_isClosed_subset
    (isClosed_horizontalSection (isClosed_symmetrization K hKcomp.isClosed) t)
    (horizontalSection_symmetrization_subset K t)

theorem horizontalMass_symmetrization_lt_one (hk : 0 < k) (K : Set E') (hKcomp : IsCompact K) (t : ℝ) :
    horizontalMass (symmetrization K) t < 1 := by
  letI : NeZero k := ⟨hk.ne'⟩
  obtain ⟨R, hR⟩ := (isCompact_horizontalSection_symmetrization K hKcomp t).isBounded.exists_norm_le
  have hs : horizontalSection (symmetrization K) t ⊆ Metric.closedBall (0 : E) R := by
    intro y hy
    simpa only [Metric.mem_closedBall, dist_zero_right] using hR y hy
  exact (measureReal_mono hs).trans_lt (gaussian_ball_mass_lt_one R)

/-- Convexity of the actual two-stage reduction has no remaining section-mass
assumption in positive horizontal dimension. -/
theorem convex_planarSymmetrization_symmetrization (hk : 0 < k) (K : Set E')
    (hKcomp : IsCompact K) (hKconv : Convex ℝ K) :
    Convex ℝ (planarSymmetrization (symmetrization K)) :=
  convex_planarSymmetrization _ (isClosed_symmetrization K hKcomp.isClosed)
    (convex_symmetrization K hKcomp hKconv) (horizontalMass_symmetrization_lt_one hk K hKcomp)

end OAI.GaussianPropeller.PlanarSymmetrization
