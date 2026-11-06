import Tusnady.Upper.Ehrhard.ModifiedVerticalFold
import Tusnady.Upper.Ehrhard.PlanarSymmetrizationClosed
import Tusnady.Upper.Ehrhard.SmallRadiusQuantile

/-!
# Exact commutation of the second symmetrization with the Gaussian fold

Closed downward fibers, including the empty set and the whole line, are
handled by a finite-CDF cutoff lemma.  The resulting set identity proves the
second reduction in Szusterman (2025), §2.1.  There is no assumed measure
monotonicity or Gaussian comparison theorem in this file.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OAI.GaussianPropeller.ModifiedFoldPlanar
open Quantile GaussianSections Symmetrization PlanarSymmetrization ModifiedVerticalFold

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem horizontalMass_symmetrization_antitone (K : Set E') :
    Antitone (horizontalMass (symmetrization K)) := by
  intro s t hst
  refine measureReal_mono (μ := gaussianMeasure (Fin k)) ?_
  intro y hy
  change append y s ∈ symmetrization K
  change Φ (last (append y s)) ≤ sectionMass K (front (append y s))
  rw [append_last, front_append]
  have ht : Φ t ≤ sectionMass K y := by simpa [horizontalSection, symmetrization] using hy
  exact (strictMono_Φ.monotone hst).trans ht

/-- Closed downward scalar sets are exactly determined by each interior
Gaussian quantile, with no excluded empty or full-set case. -/
theorem gaussian_mass_cutoff_iff (J : Set ℝ) (hJ : IsClosed J)
    (hdown : ∀ s t, s ≤ t → t ∈ J → s ∈ J) (p : ℝ) (hp : p ∈ Ioo (0 : ℝ) 1) :
    p ≤ (gaussianReal 0 1).real J ↔ q p ∈ J := by
  constructor
  · intro hm
    by_contra hnot
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJ.isOpen_compl (q p) hnot
    let a : ℝ := q p - ε / 2
    have ha : a < q p := by dsimp [a]; linarith
    have haNot : a ∉ J := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      dsimp [a]
      rw [show q p - ε / 2 - q p = -ε / 2 by ring, abs_div, abs_neg, abs_of_pos hε]
      norm_num
      linarith
    have hs : J ⊆ Iic a := by
      intro t ht
      by_contra h
      exact haNot (hdown a t (not_le.mp h).le ht)
    have hlt : (gaussianReal 0 1).real (Iic a) < p := by
      rw [← cdf_eq_gaussianReal]
      exact (strictMono_Φ ha).trans_eq (Φ_q hp)
    exact (not_lt_of_ge hm) ((measureReal_mono hs).trans_lt hlt)
  · intro hq
    have hs : Iic (q p) ⊆ J := fun s hs => hdown s (q p) hs hq
    have hm := measureReal_mono (μ := gaussianReal 0 1) hs
    rwa [← cdf_eq_gaussianReal, Φ_q hp] at hm

private theorem mem_planar_append (B : Set E') (x : EuclideanSpace ℝ (Fin 1)) (t : ℝ) :
    append x t ∈ planarSymmetrization B ↔ Φ (x 0) ≤ horizontalMass B t := by
  change Φ (append x t (0 : Fin 1).castSucc) ≤ horizontalMass B (last (append x t)) ↔ _
  rw [append_castSucc, append_last]

theorem horizontalSection_fold_symmetrization (K : Set E') {r : ℝ} (hr : 0 ≤ r)
    (hp : intervalMass r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    horizontalSection (gaussianVerticalFold (symmetrization K) r) t =
      horizontalSection (symmetrization K) (max (q (intervalMass r)) (t - r)) := by
  ext y
  change append y t ∈ gaussianVerticalFold (symmetrization K) r ↔ _
  rw [fold_symmetrization K hr]
  simp only [horizontalSection, symmetrization, mem_setOf_eq, front_append, append_last]
  have hq := Φ_q hp
  rcases le_total (q (intervalMass r)) (t - r) with h | h
  · rw [max_eq_right h]
    constructor
    · exact And.right
    · intro ht
      exact ⟨(show intervalMass r ≤ Φ (t - r) by rw [← hq]; exact strictMono_Φ.monotone h).trans ht, ht⟩
  · rw [max_eq_left h, hq]
    constructor
    · exact And.left
    · intro ht
      exact ⟨ht, (strictMono_Φ.monotone h).trans (by rwa [hq])⟩

theorem horizontalMass_fold_symmetrization (K : Set E') {r : ℝ} (hr : 0 ≤ r)
    (hp : intervalMass r ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    horizontalMass (gaussianVerticalFold (symmetrization K) r) t =
      horizontalMass (symmetrization K) (max (q (intervalMass r)) (t - r)) := by
  unfold horizontalMass
  rw [horizontalSection_fold_symmetrization K hr hp]

theorem cutoff_planarSymmetrization (K : Set E') (hK : IsClosed K) {r : ℝ}
    (hp : intervalMass r ∈ Ioo (0 : ℝ) 1) (x : EuclideanSpace ℝ (Fin 1)) :
    intervalMass r ≤ sectionMass (planarSymmetrization (symmetrization K)) x ↔
      Φ (x 0) ≤ horizontalMass (symmetrization K) (q (intervalMass r)) := by
  let L := planarSymmetrization (symmetrization K)
  have hLc : IsClosed L := isClosed_planarSymmetrization _ (isClosed_symmetrization K hK)
  have hdown : ∀ s t, s ≤ t → t ∈ verticalSection L x → s ∈ verticalSection L x := by
    intro s t hst ht
    have hht : Φ (x 0) ≤ horizontalMass (symmetrization K) t := (mem_planar_append _ x t).1 ht
    exact (mem_planar_append _ x s).2
      (hht.trans (horizontalMass_symmetrization_antitone K hst))
  have hh := gaussian_mass_cutoff_iff (verticalSection L x)
    (isClosed_verticalSection hLc x) hdown (intervalMass r) hp
  exact hh.trans (mem_planar_append _ x _)

private theorem planar_axis_zero (z : Plane) (s : ℝ) : (z - axis (k := 1) s) 0 = z 0 := by
  change (z - axis (k := 1) s) (0 : Fin 1).castSucc = z (0 : Fin 1).castSucc
  simp [axis, append]

theorem enlargement_planarSymmetrization (K : Set E') {r : ℝ} (hr : 0 ≤ r) (z : Plane) :
    z ∈ verticalEnlargement (planarSymmetrization (symmetrization K)) r ↔
      Φ (z 0) ≤ horizontalMass (symmetrization K) (last z - r) := by
  rw [mem_verticalEnlargement]
  constructor
  · rintro ⟨s, hs, hz⟩
    change Φ ((z - axis (k := 1) s) 0) ≤ horizontalMass (symmetrization K) (last (z - axis (k := 1) s)) at hz
    rw [planar_axis_zero, last_sub_axis] at hz
    exact hz.trans (horizontalMass_symmetrization_antitone K (by linarith [hs.2]))
  · intro hz
    refine ⟨r, ⟨by linarith, le_rfl⟩, ?_⟩
    change Φ ((z - axis (k := 1) r) 0) ≤ horizontalMass (symmetrization K) (last (z - axis (k := 1) r))
    simpa only [planar_axis_zero, last_sub_axis] using hz

/-- Exact second-stage commutation, before taking Gaussian measures. -/
theorem planarSymmetrization_fold_symmetrization (K : Set E') (hK : IsClosed K)
    {r : ℝ} (hr : 0 ≤ r) (hp : intervalMass r ∈ Ioo (0 : ℝ) 1) :
    planarSymmetrization (gaussianVerticalFold (symmetrization K) r) =
      gaussianVerticalFold (planarSymmetrization (symmetrization K)) r := by
  ext z
  change Φ (z 0) ≤ horizontalMass (gaussianVerticalFold (symmetrization K) r) (last z) ↔ _
  rw [horizontalMass_fold_symmetrization K hr hp]
  change Φ (z 0) ≤ horizontalMass (symmetrization K) (max (q (intervalMass r)) (last z - r)) ↔
    z ∈ verticalEnlargement (planarSymmetrization (symmetrization K)) r ∧
      intervalMass r ≤ sectionMass (planarSymmetrization (symmetrization K)) (front z)
  rw [enlargement_planarSymmetrization K hr z, cutoff_planarSymmetrization K hK hp]
  have hf : front z (0 : Fin 1) = z 0 := rfl
  rw [hf]
  rcases le_total (q (intervalMass r)) (last z - r) with h | h
  · rw [max_eq_right h]
    constructor
    · intro hz
      exact ⟨hz, hz.trans (horizontalMass_symmetrization_antitone K h)⟩
    · exact And.left
  · rw [max_eq_left h]
    constructor
    · intro hz
      exact ⟨hz.trans (horizontalMass_symmetrization_antitone K h), hz⟩
    · exact And.right

/-- The genuine Gaussian measure identity for the second fold reduction. -/
theorem gaussian_mass_fold_planarSymmetrization (K : Set E') (hK : IsClosed K)
    {r : ℝ} (hr : 0 ≤ r) (hp : intervalMass r ∈ Ioo (0 : ℝ) 1) :
    (gaussianMeasure (Fin 2)).real
        (gaussianVerticalFold (planarSymmetrization (symmetrization K)) r) =
      (gaussianMeasure (Fin (k + 1))).real (gaussianVerticalFold (symmetrization K) r) := by
  rw [← planarSymmetrization_fold_symmetrization K hK hr hp]
  exact gaussian_mass_planarSymmetrization _
    (measurableSet_gaussianVerticalFold _ (isClosed_symmetrization K hK) r)

/-- The numerical radius needed later is itself proved, not assumed. -/
theorem planarSymmetrization_fold_smallRadius (K : Set E') (hK : IsClosed K)
    {r : ℝ} (hr : 0 < r) (hsmall : r ≤ (1 : ℝ) / 1000) :
    planarSymmetrization (gaussianVerticalFold (symmetrization K) r) =
      gaussianVerticalFold (planarSymmetrization (symmetrization K)) r :=
  planarSymmetrization_fold_symmetrization K hK hr.le (SmallRadiusQuantile.small_radius_quantile hr hsmall).1

end OAI.GaussianPropeller.ModifiedFoldPlanar
