import Tusnady.Upper.Ehrhard.ModifiedVerticalFold
import Tusnady.Upper.Ehrhard.SmallRadiusQuantile
import Tusnady.LiteratureAnderson
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Order.Compact

/-!
# The Gaussian fold is contained in the actual Banaszczyk fold

The interval-width implication is proved using the already proved Anderson
theorem, with all scalar/product Gaussian transport discharged.  The final
containment has no width, centering, or comparison hypothesis: compactness,
convexity, and positive radius are its only inputs.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Pointwise RealInnerProductSpace

namespace OAI.GaussianPropeller.ModifiedFoldContainment
open Quantile GaussianSections Symmetrization ModifiedVerticalFold

theorem scalarGaussian_anderson (J : Set ℝ) (hJc : IsClosed J) (hJv : Convex ℝ J)
    (hJs : ∀ x : ℝ, x ∈ J ↔ -x ∈ J) (m : ℝ) :
    (gaussianReal 0 1).real {x | x - m ∈ J} ≤ (gaussianReal 0 1).real J := by
  let V : Set (Fin 1 → ℝ) := {x | x 0 ∈ J}
  have hVc : IsClosed V := hJc.preimage (continuous_apply 0)
  have hVv : Convex ℝ V := by
    intro x hx y hy a b ha hb hab
    exact hJv hx hy ha hb hab
  have hVs : ∀ x : Fin 1 → ℝ, x ∈ V ↔ -x ∈ V := fun x => hJs (x 0)
  have h := Tusnady.LiteratureGaussian.linearImage_anderson
    Tusnady.LiteratureProof.gaussianMidpointIntegralBound
    (ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) V hVc hVv hVs (fun _ => m)
  have hlaw : (Tusnady.Literature.standardGaussian 1).map (fun z : Fin 1 → ℝ => z 0) =
      gaussianReal 0 1 := (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq
  have hevent : MeasurableSet {x : ℝ | x - m ∈ J} := hJc.measurableSet.preimage (by fun_prop)
  have hraw : (gaussianReal 0 1) {x | x - m ∈ J} ≤ (gaussianReal 0 1) J := by
    rw [← hlaw, Measure.map_apply (measurable_pi_apply 0) hevent,
      Measure.map_apply (measurable_pi_apply 0) hJc.measurableSet]
    change (Tusnady.Literature.standardGaussian 1) {x | x 0 - m ∈ J} ≤
      (Tusnady.Literature.standardGaussian 1) {x | x 0 ∈ J}
    simpa only [V, ContinuousLinearMap.id_apply, mem_setOf_eq, Pi.sub_apply] using h
  exact ENNReal.toReal_mono (measure_ne_top _ _) hraw

theorem gaussian_interval_mass_le_centered (a b : ℝ) :
    (gaussianReal 0 1).real (Icc a b) ≤
      (gaussianReal 0 1).real (Icc (-((b - a) / 2)) ((b - a) / 2)) := by
  let R := (b - a) / 2
  let m := (a + b) / 2
  have hs : ∀ x : ℝ, x ∈ Icc (-R) R ↔ -x ∈ Icc (-R) R := by
    intro x
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have heq : {x : ℝ | x - m ∈ Icc (-R) R} = Icc a b := by
    ext x
    simp only [mem_setOf_eq, mem_Icc]
    dsimp [m, R]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have h := scalarGaussian_anderson (Icc (-R) R) isClosed_Icc (convex_Icc _ _) hs m
  rwa [heq] at h

theorem gaussian_Icc_mass_eq_cdf_sub (a b : ℝ) (hab : a ≤ b) :
    (gaussianReal 0 1).real (Icc a b) = Φ b - Φ a := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)
  have hs : Iio a ⊆ Iic b := fun x hx => hx.le.trans hab
  have hset : Iic b \ Iio a = Icc a b := by
    ext x
    simp only [mem_sdiff, mem_Iic, mem_Iio, not_lt, mem_Icc, and_comm]
  rw [← hset, measureReal_diff hs measurableSet_Iio,
    measureReal_congr (Iio_ae_eq_Iic (μ := gaussianReal 0 1) (a := a)),
    ← cdf_eq_gaussianReal, ← cdf_eq_gaussianReal]

theorem centered_interval_mass_strictMono {R r : ℝ} (hR : 0 ≤ R) (hRr : R < r) :
    (gaussianReal 0 1).real (Icc (-R) R) < (gaussianReal 0 1).real (Icc (-r) r) := by
  rw [gaussian_Icc_mass_eq_cdf_sub _ _ (by linarith),
    gaussian_Icc_mass_eq_cdf_sub _ _ (by linarith), Φ_neg, Φ_neg]
  linarith [strictMono_Φ hRr]

/-- The cutoff forces a genuine Euclidean width, not an assumed width. -/
theorem interval_width_of_gaussian_mass (a b : ℝ) (hab : a ≤ b) {r : ℝ}
    (hm : intervalMass r ≤ (gaussianReal 0 1).real (Icc a b)) : 2 * r ≤ b - a := by
  by_contra hwidth
  have hR : 0 ≤ (b - a) / 2 := by linarith
  have hRr : (b - a) / 2 < r := by linarith
  have hcenter := gaussian_interval_mass_le_centered a b
  have hstrict := centered_interval_mass_strictMono hR hRr
  exact (not_lt_of_ge hm) (hcenter.trans_lt hstrict)

theorem interval_enlargement_subset_signingFold (a b : ℝ) {r : ℝ} (hr : 0 < r)
    (hwidth : 2 * r ≤ b - a) :
    Icc a b + Icc (-r) r ⊆ Tusnady.Upper.signingFold r (Icc a b) := by
  rintro x ⟨s, hs, t, ht, rfl⟩
  have hxlo : a - r ≤ s + t := by linarith [hs.1, ht.1]
  have hxhi : s + t ≤ b + r := by linarith [hs.2, ht.2]
  by_cases hlo : s + t ≤ a + r
  · apply (Tusnady.Upper.mem_signingFold_iff (Icc a b) r (s + t)).2
    refine ⟨a + r, (s + t - (a + r)) / r, ⟨by linarith, by linarith⟩,
      ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · exact ⟨(le_div_iff₀ hr).2 (by linarith), (div_le_iff₀ hr).2 (by linarith)⟩
    · simp only [smul_eq_mul]
      field_simp
      ring
  · by_cases hhi : b - r ≤ s + t
    · apply (Tusnady.Upper.mem_signingFold_iff (Icc a b) r (s + t)).2
      refine ⟨b - r, (s + t - (b - r)) / r, ⟨by linarith, by linarith⟩,
        ⟨by linarith, by linarith⟩, ?_, ?_⟩
      · exact ⟨(le_div_iff₀ hr).2 (by linarith), (div_le_iff₀ hr).2 (by linarith)⟩
      · simp only [smul_eq_mul]
        field_simp
        ring
    · apply (Tusnady.Upper.mem_signingFold_iff (Icc a b) r (s + t)).2
      exact ⟨s + t, 0, ⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
        by norm_num, by simp⟩

/-- The actual Gaussian variant is contained in the actual Banaszczyk fold.
The width implication and all Gaussian transport are proved above. -/
theorem gaussianVerticalFold_subset_signingFold {k : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin (k + 1)))) (hKc : IsCompact K) (hKv : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) :
    gaussianVerticalFold K r ⊆ Tusnady.Upper.signingFold (axis r) K := by
  intro z hz
  let y := front z
  let I := verticalSection K y
  have hImass : intervalMass r ≤ (gaussianReal 0 1).real I := hz.2
  have hIp : 0 < (gaussianReal 0 1).real I :=
    (SmallRadiusQuantile.intervalMass_pos hr).trans_le hImass
  have hIn := nonempty_of_measureReal_ne_zero hIp.ne'
  have hIc := isCompact_verticalSection K hKc y
  have hIv := convex_verticalSection K hKv y
  have hIeq := eq_Icc_of_connected_compact (hIv.isConnected hIn) hIc
  let a := sInf I
  let b := sSup I
  have hIeq' : I = Icc a b := hIeq
  have hab : a ≤ b := csInf_le_csSup hIn hIc.bddBelow hIc.bddAbove
  have hwidth : 2 * r ≤ b - a := interval_width_of_gaussian_mass a b hab (by rwa [← hIeq'])
  have henlarge : last z ∈ I + Icc (-r) r := by
    rw [← verticalSection_enlargement_eq_add K r y]
    change append (front z) (last z) ∈ verticalEnlargement K r
    simpa only [append_front_last] using hz.1
  have hscalar : last z ∈ Tusnady.Upper.signingFold r I := by
    rw [hIeq'] at henlarge ⊢
    exact interval_enlargement_subset_signingFold a b hr hwidth henlarge
  rw [← verticalSection_signingFold K r y] at hscalar
  change append (front z) (last z) ∈ Tusnady.Upper.signingFold (axis r) K at hscalar
  simpa only [append_front_last] using hscalar

end OAI.GaussianPropeller.ModifiedFoldContainment
