import Tusnady.Upper.Ehrhard.SymmetrizationClosed
import Mathlib.Topology.Algebra.Group.Pointwise

/-!
# The Gaussian variant of the vertical Banaszczyk fold

This is the concrete transform in Szusterman (2025), equation (4): enlarge
vertically by [-r,r], retaining the fibers whose Gaussian mass is at least
the mass of that centered interval.  No measure monotonicity is asserted yet.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Pointwise RealInnerProductSpace
namespace OAI.GaussianPropeller.ModifiedVerticalFold
open Quantile GaussianSections Symmetrization
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k+1))

def intervalMass (r : ℝ) : ℝ := (gaussianReal 0 1).real (Icc (-r) r)
def verticalSegment (r : ℝ) : Set E' := axis '' Icc (-r) r
def verticalEnlargement (K : Set E') (r : ℝ) : Set E' := K + verticalSegment r
def gaussianVerticalFold (K : Set E') (r : ℝ) : Set E' :=
  verticalEnlargement K r ∩ {z | intervalMass r ≤ sectionMass K (front z)}

theorem mem_verticalEnlargement (K : Set E') (r : ℝ) (z : E') :
    z ∈ verticalEnlargement K r ↔ ∃ s ∈ Icc (-r) r, z - axis s ∈ K := by
  constructor
  · rintro ⟨x, hx, _, ⟨s, hs, rfl⟩, rfl⟩
    exact ⟨s, hs, by simpa using hx⟩
  · rintro ⟨s, hs, hz⟩
    exact ⟨z - axis s, hz, axis s, ⟨s, hs, rfl⟩, sub_add_cancel z (axis s)⟩

theorem isCompact_verticalSegment (r : ℝ) : IsCompact (verticalSegment (k := k) r) :=
  isCompact_Icc.image (continuous_append.comp (continuous_const.prodMk continuous_id))

theorem isClosed_verticalEnlargement (K : Set E') (hK : IsClosed K) (r : ℝ) :
    IsClosed (verticalEnlargement K r) :=
  hK.add_right_of_isCompact (isCompact_verticalSegment r)

theorem measurableSet_gaussianVerticalFold (K : Set E') (hK : IsClosed K) (r : ℝ) :
    MeasurableSet (gaussianVerticalFold K r) := by
  exact (isClosed_verticalEnlargement K hK r).measurableSet.inter
    (measurableSet_le measurable_const
      ((measurable_sectionMass hK.measurableSet).comp continuous_front.measurable))

theorem verticalSection_enlargement (K : Set E') (r : ℝ) (y : E) :
    verticalSection (verticalEnlargement K r) y =
      {t | ∃ s ∈ Icc (-r) r, t - s ∈ verticalSection K y} := by
  ext t
  simp only [verticalSection, mem_setOf_eq, mem_verticalEnlargement, append_sub_axis]

theorem verticalSection_enlargement_eq_add (K : Set E') (r : ℝ) (y : E) :
    verticalSection (verticalEnlargement K r) y = verticalSection K y + Icc (-r) r := by
  rw [verticalSection_enlargement]
  ext t
  constructor
  · rintro ⟨s, hs, ht⟩
    exact ⟨t-s, ht, s, hs, sub_add_cancel t s⟩
  · rintro ⟨x, hx, s, hs, rfl⟩
    exact ⟨s, hs, by simpa using hx⟩

theorem isCompact_verticalSection (K : Set E') (hK : IsCompact K) (y : E) :
    IsCompact (verticalSection K y) := by
  apply (hK.image continuous_last).of_isClosed_subset (isClosed_verticalSection hK.isClosed y)
  intro t ht
  exact ⟨append y t, ht, append_last y t⟩

theorem convex_verticalSection (K : Set E') (hK : Convex ℝ K) (y : E) :
    Convex ℝ (verticalSection K y) := by
  intro s hs t ht a b ha hb hab
  have h := hK hs ht ha hb hab
  have heq : a • append y s + b • append y t = append y (a*s+b*t) := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [append]
    · simp only [PiLp.add_apply, PiLp.smul_apply, append_castSucc, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
  change append y (a*s+b*t) ∈ K
  simpa only [heq] using h

theorem verticalSection_fold (K : Set E') (r : ℝ) (y : E) :
    verticalSection (gaussianVerticalFold K r) y =
      if intervalMass r ≤ sectionMass K y then verticalSection K y + Icc (-r) r else ∅ := by
  classical
  ext t
  simp only [verticalSection, gaussianVerticalFold, mem_setOf_eq, mem_inter_iff, front_append]
  by_cases h : intervalMass r ≤ sectionMass K y
  · simp only [h, and_true, ↓reduceIte]
    exact Set.ext_iff.mp (verticalSection_enlargement_eq_add K r y) t
  · simp [h]

theorem front_sub_axis (z : E') (s : ℝ) : front (z - axis s) = front z := by
  ext i
  simp [front, axis, append]

theorem last_sub_axis (z : E') (s : ℝ) : last (z - axis s) = last z - s := by
  simp [last, axis, append]

theorem sectionMass_symmetrization (K : Set E') (y : E) :
    sectionMass (symmetrization K) y = sectionMass K y := by
  change (gaussianReal 0 1).real (verticalSection (symmetrization K) y) = sectionMass K y
  rw [verticalSection_symmetrization]
  exact gaussian_cdf_sublevel_mass _ (sectionMass_mem K y)

theorem enlargement_symmetrization (K : Set E') {r : ℝ} (hr : 0 ≤ r) :
    verticalEnlargement (symmetrization K) r =
      {z | Φ (last z - r) ≤ sectionMass K (front z)} := by
  ext z
  rw [mem_verticalEnlargement]
  constructor
  · rintro ⟨s, hs, hz⟩
    change Φ (last (z - axis s)) ≤ sectionMass K (front (z - axis s)) at hz
    rw [last_sub_axis, front_sub_axis] at hz
    exact (strictMono_Φ.monotone (by linarith [hs.2])).trans hz
  · intro hz
    change Φ (last z - r) ≤ sectionMass K (front z) at hz
    refine ⟨r, ⟨by linarith, le_refl r⟩, ?_⟩
    change Φ (last (z - axis r)) ≤ sectionMass K (front (z - axis r))
    simpa only [last_sub_axis, front_sub_axis] using hz

/-- The modified fold of a symmetrized set is an explicit clipped hypograph,
with finite CDF values even when some original fibers have mass zero or one. -/
theorem fold_symmetrization (K : Set E') {r : ℝ} (hr : 0 ≤ r) :
    gaussianVerticalFold (symmetrization K) r =
      {z | intervalMass r ≤ sectionMass K (front z) ∧
        Φ (last z - r) ≤ sectionMass K (front z)} := by
  ext z
  simp only [gaussianVerticalFold, enlargement_symmetrization K hr, mem_inter_iff,
    mem_setOf_eq, sectionMass_symmetrization]
  exact and_comm

theorem verticalSection_fold_symmetrization (K : Set E') {r : ℝ} (hr : 0 ≤ r) (y : E) :
    verticalSection (gaussianVerticalFold (symmetrization K) r) y =
      if intervalMass r ≤ sectionMass K y then {t | Φ (t-r) ≤ sectionMass K y} else ∅ := by
  classical
  rw [fold_symmetrization K hr]
  ext t
  simp only [verticalSection, mem_setOf_eq, front_append, append_last]
  by_cases h : intervalMass r ≤ sectionMass K y <;> simp [h]

theorem gaussian_cdf_translated_sublevel_mass {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (r : ℝ) :
    (gaussianReal 0 1).real {t | Φ (t-r) ≤ p} = Φ (q p + r) := by
  have heq : {t : ℝ | Φ (t-r) ≤ p} = Iic (q p + r) := by
    ext t
    change Φ (t-r) ≤ p ↔ t ≤ q p+r
    calc
      _ ↔ Φ (t-r) ≤ Φ (q p) := by rw [Φ_q hp]
      _ ↔ t-r ≤ q p := strictMono_Φ.le_iff_le
      _ ↔ t ≤ q p+r := sub_le_iff_le_add
  rw [heq, ← cdf_eq_gaussianReal]

theorem integrable_verticalSection_mass (K : Set E') (hK : MeasurableSet K) :
    Integrable (fun y : E => (gaussianReal 0 1).real (verticalSection K y))
      (gaussianMeasure (Fin k)) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_verticalSection_mass hK).ennreal_toReal.aestronglyMeasurable
  exact ae_of_all _ (fun y => by
    change ‖(gaussianReal 0 1).real (verticalSection K y)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    simpa using measureReal_mono (μ := gaussianReal 0 1) (subset_univ (verticalSection K y)))

end OAI.GaussianPropeller.ModifiedVerticalFold
