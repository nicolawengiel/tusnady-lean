import Tusnady.SamplingSpaceL2

/-!
# Characterization by actual piecewise-affine representatives

The function space is proved equal to the set of actual functions that are
affine on every real dyadic half-open cell and zero outside `[0,1)`.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace
open DyadicFunctions

def PiecewiseAffine (j : ℕ) (f : ℝ → ℝ) : Prop :=
  (∀ x, x ∉ Ico (0 : ℝ) 1 → f x = 0) ∧
    ∀ i : Fin (2 ^ j), ∃ A B : ℝ,
      EqOn f (fun x => A * x + B) (dyadicInterval j i)

lemma pointwiseSynthesis_zero_outside (j : ℕ) (a : BasisIndex j → ℝ) (x : ℝ)
    (hx : x ∉ Ico (0 : ℝ) 1) : pointwiseSynthesis j a x = 0 := by
  rw [pointwiseSynthesis_apply]
  apply Finset.sum_eq_zero
  intro ib _
  have hnot : x ∉ dyadicInterval j ib.1 := fun h => hx (dyadicInterval_subset_unit j ib.1 h)
  rw [basis_zero_outside j ib x hnot, mul_zero]

/-- On one cell only its two local coefficients contribute. -/
theorem pointwiseSynthesis_on_cell (j : ℕ) (a : BasisIndex j → ℝ)
    (i : Fin (2 ^ j)) (x : ℝ) (hx : x ∈ dyadicInterval j i) :
    pointwiseSynthesis j a x = Real.sqrt ((2 : ℝ) ^ j) *
      (a (i, false) + a (i, true) * Real.sqrt 3 * (2 * localCoordinate j i x - 1)) := by
  classical
  have hn := (localCoordinate_mem_iff j i x).mpr hx
  rw [pointwiseSynthesis_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp [basis, baseBasis, unitPatch, hn, affineMode]
    ring
  · intro k _ hki
    have hnot : x ∉ dyadicInterval j k := fun hk =>
      (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth j k i hki)) hk hx
    apply Finset.sum_eq_zero
    intro b _
    rw [basis_zero_outside j (k, b) x hnot, mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_univ i))

theorem pointwiseSynthesis_piecewiseAffine (j : ℕ) (a : BasisIndex j → ℝ) :
    PiecewiseAffine j (pointwiseSynthesis j a) := by
  refine ⟨pointwiseSynthesis_zero_outside j a, ?_⟩
  intro i
  let q := Real.sqrt ((2 : ℝ) ^ j)
  refine ⟨q * a (i, true) * Real.sqrt 3 * 2 / dyadicLength j,
    q * (a (i, false) - a (i, true) * Real.sqrt 3 *
      (2 * dyadicLeft j i / dyadicLength j + 1)), ?_⟩
  intro x hx
  rw [pointwiseSynthesis_on_cell j a i x hx]
  dsimp [q, localCoordinate]
  ring

/-- Every actual affine patch function has explicit normalized basis
coefficients. The endpoint convention is preserved exactly. -/
theorem piecewiseAffine_mem_pointwiseSpace (j : ℕ) (f : ℝ → ℝ)
    (hf : PiecewiseAffine j f) : f ∈ pointwiseSpace j := by
  classical
  choose A B hAB using hf.2
  let q := Real.sqrt ((2 : ℝ) ^ j)
  let a : BasisIndex j → ℝ := fun ib =>
    if ib.2 then A ib.1 * dyadicLength j / (2 * q * Real.sqrt 3)
    else (A ib.1 * (dyadicLeft j ib.1 + dyadicLength j / 2) + B ib.1) / q
  refine ⟨a, ?_⟩
  funext x
  by_cases hx : x ∈ Ico (0 : ℝ) 1
  · obtain ⟨i, hi, _⟩ := Haar.existsUnique_unit_interval j x hx
    rw [pointwiseSynthesis_on_cell j a i x hi, hAB i hi]
    have hq : q ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity : 0 < (2 : ℝ) ^ j))
    have hs : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))
    have hl : dyadicLength j ≠ 0 := ne_of_gt (dyadicLength_pos j)
    change q * _ = _
    dsimp [a, localCoordinate]
    field_simp
    ring
  · rw [pointwiseSynthesis_zero_outside j a x hx, hf.1 x hx]

theorem mem_pointwiseSpace_iff (j : ℕ) (f : ℝ → ℝ) :
    f ∈ pointwiseSpace j ↔ PiecewiseAffine j f := by
  constructor
  · rintro ⟨a, rfl⟩
    exact pointwiseSynthesis_piecewiseAffine j a
  · exact piecewiseAffine_mem_pointwiseSpace j f

/-- Nestedness of the actual pointwise affine spaces follows from the
proved real dyadic ancestor geometry. -/
theorem pointwiseSpace_mono {j k : ℕ} (hjk : j ≤ k) : pointwiseSpace j ≤ pointwiseSpace k := by
  intro f hf
  apply piecewiseAffine_mem_pointwiseSpace
  have hp := (mem_pointwiseSpace_iff j f).mp hf
  refine ⟨hp.1, ?_⟩
  intro i
  obtain ⟨A, B, hAB⟩ := hp.2 (Dyadic.ancestorIndex i j hjk)
  exact ⟨A, B, hAB.mono (dyadicInterval_subset_ancestor hjk i)⟩

/-- Almost-everywhere equality determines the actual affine representative
uniquely, including all assigned half-open endpoints. -/
theorem pointwiseSpace_ae_eq_imp_eq (j : ℕ) (f g : ℝ → ℝ)
    (hf : f ∈ pointwiseSpace j) (hg : g ∈ pointwiseSpace j) (hfg : f =ᵐ[volume] g) : f = g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  have hl2 : l2Synthesis j a = l2Synthesis j b := by
    apply Lp.ext
    exact (l2Synthesis_ae j a).trans (hfg.trans (l2Synthesis_ae j b).symm)
  exact congrArg (pointwiseSynthesis j) (l2Synthesis_injective j hl2)

theorem mem_l2Space_iff_pointwise (j : ℕ) (v : L2Real) :
    v ∈ l2Space j ↔ ∃ f : ℝ → ℝ, f ∈ pointwiseSpace j ∧ v =ᵐ[volume] f := by
  constructor
  · intro hv
    rw [l2Space_eq_range] at hv
    obtain ⟨a, rfl⟩ := hv
    exact ⟨pointwiseSynthesis j a, ⟨a, rfl⟩, l2Synthesis_ae j a⟩
  · rintro ⟨f, ⟨a, rfl⟩, hv⟩
    have heq : v = l2Synthesis j a := Lp.ext (hv.trans (l2Synthesis_ae j a).symm)
    rw [heq, l2Space_eq_range]
    exact ⟨a, rfl⟩

theorem l2Space_mono {j k : ℕ} (hjk : j ≤ k) : l2Space j ≤ l2Space k := by
  intro v hv
  obtain ⟨f, hf, hae⟩ := (mem_l2Space_iff_pointwise j v).mp hv
  exact (mem_l2Space_iff_pointwise k v).mpr ⟨f, pointwiseSpace_mono hjk hf, hae⟩

theorem canonicalRepresentative_piecewiseAffine (j : ℕ) (v : l2Space j) :
    PiecewiseAffine j (canonicalRepresentative j v) :=
  pointwiseSynthesis_piecewiseAffine j (canonicalCoefficients j v)

theorem canonicalRepresentative_unique (j : ℕ) (v : l2Space j) (f : ℝ → ℝ)
    (hf : PiecewiseAffine j f) (hae : (v : L2Real) =ᵐ[volume] f) :
    f = canonicalRepresentative j v :=
  pointwiseSpace_ae_eq_imp_eq j f _ (piecewiseAffine_mem_pointwiseSpace j f hf)
    ⟨canonicalCoefficients j v, rfl⟩ (hae.symm.trans (canonicalRepresentative_ae j v))

theorem basis_measurable (j : ℕ) (ib : BasisIndex j) : Measurable (basis j ib) := by
  rw [basis_eq_indicator]
  exact (localMode_continuous j ib).measurable.indicator measurableSet_Ico

theorem pointwiseSynthesis_measurable (j : ℕ) (a : BasisIndex j → ℝ) :
    Measurable (pointwiseSynthesis j a) := by
  have hp : pointwiseSynthesis j a = (fun x => ∑ ib, a ib * basis j ib x) :=
    funext (pointwiseSynthesis_apply j a)
  rw [hp]
  exact Finset.measurable_sum _ fun ib _ => measurable_const.mul (basis_measurable j ib)

theorem canonicalRepresentative_measurable (j : ℕ) (v : l2Space j) :
    Measurable (canonicalRepresentative j v) :=
  pointwiseSynthesis_measurable j (canonicalCoefficients j v)

theorem PiecewiseAffine.continuousOn_cell {j : ℕ} {f : ℝ → ℝ} (hf : PiecewiseAffine j f)
    (i : Fin (2 ^ j)) : ContinuousOn f
      (Ioo (dyadicLeft j i) (dyadicLeft j i + dyadicLength j)) := by
  obtain ⟨A, B, hAB⟩ := hf.2 i
  apply (show Continuous (fun x : ℝ => A * x + B) by fun_prop).continuousOn.congr
  exact hAB.mono Ioo_subset_Ico_self

end Tusnady.SamplingSpace
