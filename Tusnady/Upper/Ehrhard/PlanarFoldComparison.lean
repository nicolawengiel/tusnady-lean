import Tusnady.Upper.Ehrhard.GaussianPlane
import Tusnady.Upper.Ehrhard.ModifiedFoldPlanar
import Tusnady.Upper.Ehrhard.PlanarSupport
import Tusnady.Upper.Ehrhard.PlanarCap

/-!
# The supporting-half-plane comparison for the planar Gaussian fold

The actual modified fold of a closed planar lower convex set is expressed as
a translated cap minus a cone. Convex Gaussian isoperimetry, the proved cone
translation comparison, and the proved small-radius half-plane estimate give
Gaussian mass monotonicity at every finite horizontal section endpoint.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Pointwise Topology NNReal ENNReal
namespace OAI.GaussianPropeller.PlanarFoldComparison
open Quantile GaussianSections Symmetrization ModifiedVerticalFold
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Vertical translation in the actual Euclidean plane. -/
def translate (L : Set Plane) (r : ℝ) : Set Plane := L + {PlanarCap.point 0 r}

def cone (c s D cut : ℝ) : Set Plane := {z | cut < z 0 ∧ c*z 0+s*z 1 ≤ D}

lemma point_eq_support (x y : ℝ) : PlanarCap.point x y = PlanarSupport.point x y := by
  ext i
  fin_cases i <;> rfl

lemma axis_eq_point (r : ℝ) : axis (k := 1) r = PlanarCap.point 0 r := by
  ext i
  fin_cases i
  · rfl
  · change last (axis (k := 1) r) = r
    simp [axis]

lemma append_front_eq_point (z : Plane) (t : ℝ) :
    append (front z) t = PlanarCap.point (z 0) t := by
  ext i
  fin_cases i
  · rfl
  · change last (append (front z) t) = t
    exact append_last _ _

lemma mem_translate (L : Set Plane) (r : ℝ) (z : Plane) :
    z ∈ translate L r ↔ z - PlanarCap.point 0 r ∈ L := by
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    have hy' : y = PlanarCap.point 0 r := hy
    subst y
    simpa using hx
  · intro hz
    exact ⟨z-PlanarCap.point 0 r, hz, PlanarCap.point 0 r, mem_singleton _, by abel⟩

lemma isClosed_translate {L : Set Plane} (hL : IsClosed L) (r : ℝ) :
    IsClosed (translate L r) := hL.add_right_of_isCompact isCompact_singleton

lemma measurableSet_cone (c s D cut : ℝ) : MeasurableSet (cone c s D cut) := by
  exact (HalfplaneFold.measurableSet_cone c s D cut).preimage
    GaussianPlane.planeProductEquiv.continuous.measurable

/-- Lower closure turns the symmetric vertical enlargement into its top
endpoint translation. -/
theorem verticalEnlargement_eq_translate (L : Set Plane) (hLower : PlanarCap.LowerClosed L)
    {r : ℝ} (hr : 0 ≤ r) : verticalEnlargement L r = translate L r := by
  ext z
  rw [mem_verticalEnlargement, mem_translate]
  constructor
  · rintro ⟨t, ht, hzt⟩
    apply hLower hzt
    intro i
    fin_cases i
    · simp [axis, append, PlanarCap.point]
    · simp only [PiLp.sub_apply]
      change z 1-r ≤ z 1-t
      linarith [ht.2]
  · intro hz
    refine ⟨r, ⟨by linarith, le_rfl⟩, ?_⟩
    simpa only [axis_eq_point] using hz

/-- The scalar quantile test in each downward fiber is exactly the finite
horizontal section test. -/
theorem mass_cutoff_iff_coordinate (L : Set Plane) (hL : IsClosed L)
    (hLower : PlanarCap.LowerClosed L) (r a : ℝ)
    (hp : intervalMass r ∈ Ioo (0 : ℝ) 1)
    (hSection : PlanarCap.horizontalSection L (q (intervalMass r)) = Iic a)
    (z : Plane) :
    intervalMass r ≤ sectionMass L (front z) ↔ z 0 ≤ a := by
  have hdown : ∀ s t : ℝ, s ≤ t → t ∈ verticalSection L (front z) →
      s ∈ verticalSection L (front z) := by
    intro s t hst ht
    apply hLower ht
    intro i
    fin_cases i
    · simp [append]
    · change last (append (front z) s) ≤ last (append (front z) t)
      simpa only [append_last] using hst
  have h := ModifiedFoldPlanar.gaussian_mass_cutoff_iff
    (verticalSection L (front z)) (isClosed_verticalSection hL (front z)) hdown
    (intervalMass r) hp
  change intervalMass r ≤ sectionMass L (front z) ↔ _ at h
  rw [h]
  change append (front z) (q (intervalMass r)) ∈ L ↔ z 0 ≤ a
  rw [append_front_eq_point]
  change z 0 ∈ PlanarCap.horizontalSection L (q (intervalMass r)) ↔ _
  rw [hSection]
  rfl

/-- The actual planar Gaussian fold is an explicitly clipped translation. -/
theorem fold_eq_translate_inter (L : Set Plane) (hL : IsClosed L)
    (hLower : PlanarCap.LowerClosed L) {r : ℝ} (hr : 0 ≤ r)
    (hp : intervalMass r ∈ Ioo (0 : ℝ) 1) (a : ℝ)
    (hSection : PlanarCap.horizontalSection L (q (intervalMass r)) = Iic a) :
    gaussianVerticalFold L r = translate L r ∩ {z : Plane | z 0 ≤ a} := by
  ext z
  simp only [gaussianVerticalFold, mem_inter_iff, mem_setOf_eq]
  rw [verticalEnlargement_eq_translate L hLower hr,
    mass_cutoff_iff_coordinate L hL hLower r a hp hSection z]

/-- Below the horizontal cut, capping adds no points. -/
lemma translate_cap_inter (L : Set Plane) (hLower : PlanarCap.LowerClosed L)
    (c s a τ r : ℝ) (hp : PlanarCap.point a τ ∈ L) :
    translate (PlanarCap.cap L c s a τ) r ∩ {z : Plane | z 0 ≤ a} =
      translate L r ∩ {z : Plane | z 0 ≤ a} := by
  ext z
  simp only [mem_inter_iff, mem_setOf_eq, mem_translate]
  constructor
  · rintro ⟨hz | hz, hza⟩
    · exact ⟨hz, hza⟩
    · refine ⟨hLower hp ?_, hza⟩
      intro i
      fin_cases i
      · simpa [PlanarCap.point] using hza
      · exact hz.1
  · rintro ⟨hz, hza⟩
    exact ⟨Or.inl hz, hza⟩

/-- The discarded supporting cone is contained in the translated cap. -/
lemma cone_subset_translate_cap (L : Set Plane) (c s a τ r : ℝ)
    (hc : 0 < c) (hs : 0 < s) :
    cone c s (c*a+s*τ+r*s) a ⊆ translate (PlanarCap.cap L c s a τ) r := by
  intro z hz
  rw [mem_translate]
  apply Or.inr
  constructor
  · change z 1-r ≤ τ
    have hn := hz.2
    have hx : c*a < c*z 0 := mul_lt_mul_of_pos_left hz.1 hc
    have hh : s*(z 1-r) ≤ s*τ := by nlinarith
    exact (mul_le_mul_iff_right₀ hs).mp hh
  · change c*(z 0-0)+s*(z 1-r) ≤ c*a+s*τ
    have hn := hz.2
    nlinarith

/-- Removing the right-hand cone is the same as clipping the translated cap. -/
lemma translate_cap_diff_cone (L : Set Plane) (c s a τ r : ℝ)
    (hSupport : ∀ z ∈ L, c*z 0+s*z 1 ≤ c*a+s*τ) :
    translate (PlanarCap.cap L c s a τ) r \ cone c s (c*a+s*τ+r*s) a =
      translate (PlanarCap.cap L c s a τ) r ∩ {z : Plane | z 0 ≤ a} := by
  ext z
  constructor
  · rintro ⟨hz, hn⟩
    refine ⟨hz, ?_⟩
    by_contra hcut
    apply hn
    refine ⟨lt_of_not_ge hcut, ?_⟩
    have hcap : z-PlanarCap.point 0 r ∈ PlanarCap.cap L c s a τ := (mem_translate _ _ _).1 hz
    have hh := PlanarCap.cap_support c s a τ hSupport hcap
    change c*(z 0-0)+s*(z 1-r) ≤ c*a+s*τ at hh
    nlinarith
  · rintro ⟨hz, hcut⟩
    exact ⟨hz, fun hn => (not_lt_of_ge hcut) hn.1⟩

/-- The exact cap-minus-cone representation used in the comparison proof. -/
theorem fold_eq_cap_diff_cone (L : Set Plane) (hL : IsClosed L)
    (hLower : PlanarCap.LowerClosed L) {r : ℝ} (hr : 0 ≤ r)
    (hp : intervalMass r ∈ Ioo (0 : ℝ) 1) (a c s : ℝ)
    (hSection : PlanarCap.horizontalSection L (q (intervalMass r)) = Iic a)
    (hSupport : ∀ z ∈ L, c*z 0+s*z 1 ≤ c*a+s*q (intervalMass r)) :
    gaussianVerticalFold L r =
      translate (PlanarCap.cap L c s a (q (intervalMass r))) r \
        cone c s (c*a+s*q (intervalMass r)+r*s) a := by
  rw [fold_eq_translate_inter L hL hLower hr hp a hSection,
    translate_cap_diff_cone L c s a (q (intervalMass r)) r hSupport,
    translate_cap_inter L hLower c s a (q (intervalMass r)) r
      (PlanarCap.anchor_mem_of_section L a _ hSection)]

/-- Exact probability of a half-plane clipped on the right. -/
lemma clipped_halfspace_mass (c s D cut : ℝ) (hunit : c^2+s^2=1) :
    (gaussianMeasure (Fin 2)).real {z : Plane | z 0 ≤ cut ∧ c*z 0+s*z 1 ≤ D} =
      Φ D - (gaussianMeasure (Fin 2)).real (cone c s D cut) := by
  have heq : {z : Plane | z 0 ≤ cut ∧ c*z 0+s*z 1 ≤ D} =
      {z : Plane | c*z 0+s*z 1 ≤ D} \ cone c s D cut := by
    ext z
    constructor
    · rintro ⟨hz, hn⟩
      exact ⟨hn, fun hh => (not_lt_of_ge hz) hh.1⟩
    · rintro ⟨hn, hh⟩
      exact ⟨le_of_not_gt (fun hz => hh ⟨hz, hn⟩), hn⟩
  rw [heq, measureReal_diff (μ := gaussianMeasure (Fin 2))
    (s₁ := {z : Plane | c*z 0+s*z 1 ≤ D}) (s₂ := cone c s D cut)
    (fun z hz => hz.2) (measurableSet_cone c s D cut),
    GaussianPlane.halfspace_mass c s hunit D]

/-- The analytic cap comparison, for a genuinely supporting nonvertical
normal. All Gaussian comparisons are proved in the imported modules. -/
theorem gaussian_mass_fold_ge_of_support (L : Set Plane) (hLc : IsClosed L)
    (hLv : Convex ℝ L) (hLower : PlanarCap.LowerClosed L)
    (hMass : (1 : ℝ)/2 ≤ (gaussianMeasure (Fin 2)).real L)
    (r : ℝ) (hr : 0 < r) (hsmall : r ≤ (1 : ℝ)/1000)
    (a c s : ℝ) (hc : 0 < c) (hs : 0 < s) (hunit : c^2+s^2=1)
    (hSection : PlanarCap.horizontalSection L (q (intervalMass r)) = Iic a)
    (hSupport : ∀ z ∈ L, c*z 0+s*z 1 ≤ c*a+s*q (intervalMass r)) :
    (gaussianMeasure (Fin 2)).real L ≤
      (gaussianMeasure (Fin 2)).real (gaussianVerticalFold L r) := by
  let τ := q (intervalMass r)
  let w := -τ
  let A := PlanarCap.cap L c s a τ
  let D := c*a+s*τ
  let d := q ((gaussianMeasure (Fin 2)).real A)
  have hnum := SmallRadiusQuantile.small_radius_quantile hr hsmall
  have hp : intervalMass r ∈ Ioo (0 : ℝ) 1 := hnum.1
  have hw : 0 ≤ w := by
    have hh : 2 ≤ w-r := hnum.2.1
    linarith
  have hanchor : PlanarCap.point a τ ∈ L :=
    PlanarCap.anchor_mem_of_section L a τ hSection
  have hAc : IsClosed A := PlanarCap.isClosed_cap hLc c s a τ
  have hAv : Convex ℝ A := PlanarCap.convex_cap hLv hLower c s a τ hc hanchor hSupport
  have hLA : L ⊆ A := PlanarCap.subset_cap L c s a τ
  have hAhalf : (1 : ℝ)/2 ≤ (gaussianMeasure (Fin 2)).real A :=
    hMass.trans (measureReal_mono hLA)
  have hAsupport : A ⊆ {z : Plane | c*z 0+s*z 1 ≤ D} := by
    intro z hz
    exact PlanarCap.cap_support c s a τ hSupport hz
  have hAbound : (gaussianMeasure (Fin 2)).real A ≤ Φ D :=
    (measureReal_mono hAsupport).trans_eq (GaussianPlane.halfspace_mass c s hunit D)
  have hAm : (gaussianMeasure (Fin 2)).real A ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith, hAbound.trans_lt (Φ_lt_one D)⟩
  have hPhi : Φ d = (gaussianMeasure (Fin 2)).real A := Φ_q hAm
  have hd : 0 ≤ d := by
    apply strictMono_Φ.le_iff_le.mp
    rw [Φ_zero, hPhi]
    exact hAhalf
  have hdD : d ≤ D := by
    apply strictMono_Φ.le_iff_le.mp
    rw [hPhi]
    exact hAbound
  have hiso := closedConvex_gaussian_isoperimetry_general (by decide : 0 < 2)
    A hAc hAv hAm (mul_nonneg hr.le hs.le)
  have hball : A + Metric.closedBall (0 : Plane) (r*s) ⊆ translate A r :=
    PlanarCap.cap_add_closedBall_subset_translate hLv hLower c s a τ hc hs hunit
      hanchor hSupport hr.le
  have htrans : Φ (d+r*s) ≤ (gaussianMeasure (Fin 2)).real (translate A r) :=
    hiso.trans (measureReal_mono hball)
  have hfold := fold_eq_cap_diff_cone L hLc hLower hr.le hp a c s hSection hSupport
  have hsubset : cone c s (D+r*s) a ⊆ translate A r :=
    cone_subset_translate_cap L c s a τ r hc hs
  have hfoldmass : (gaussianMeasure (Fin 2)).real (gaussianVerticalFold L r) =
      (gaussianMeasure (Fin 2)).real (translate A r) -
        (gaussianMeasure (Fin 2)).real (cone c s (D+r*s) a) := by
    rw [hfold]
    exact measureReal_diff hsubset (measurableSet_cone c s (D+r*s) a)
  have hcut : (D+s*w)/c = a := by
    dsimp only [D, w, τ]
    field_simp [hc.ne']
    ring
  have hcone := GaussianPlane.supporting_cone_mass_le c s D d r w hc hs hd hdD hw
  change (gaussianMeasure (Fin 2)).real (cone c s (D+r*s) ((D+s*w)/c)) ≤
    (gaussianMeasure (Fin 2)).real (cone c s (d+r*s) ((d+s*w)/c)) at hcone
  rw [hcut] at hcone
  have hhalf := GaussianPlane.halfplane_fold_mass_of_small_radius c s d r hc hs hunit hd hr hsmall
  change Φ d ≤ (gaussianMeasure (Fin 2)).real
    {z : Plane | z 0 ≤ (d+s*w)/c ∧ c*z 0+s*z 1 ≤ d+r*s} at hhalf
  rw [clipped_halfspace_mass c s (d+r*s) ((d+s*w)/c) hunit, hPhi] at hhalf
  have hcomp : (gaussianMeasure (Fin 2)).real A ≤
      (gaussianMeasure (Fin 2)).real (gaussianVerticalFold L r) := by
    rw [hfoldmass]
    linarith
  exact (measureReal_mono hLA).trans hcomp

/-- The planar fold comparison at a finite horizontal section endpoint.
The supporting half-plane is constructed from closed convex geometry, and the
vertical supporting-line case is included. No analytic or geometric existence
statement is supplied as an additional premise. -/
theorem gaussian_mass_fold_ge_of_finite_section (L : Set Plane) (hLc : IsClosed L)
    (hLv : Convex ℝ L) (hLower : PlanarCap.LowerClosed L)
    (hMass : (1 : ℝ)/2 ≤ (gaussianMeasure (Fin 2)).real L)
    (r : ℝ) (hr : 0 < r) (hsmall : r ≤ (1 : ℝ)/1000) (a : ℝ)
    (hSection : PlanarCap.horizontalSection L (q (intervalMass r)) = Iic a) :
    (gaussianMeasure (Fin 2)).real L ≤
      (gaussianMeasure (Fin 2)).real (gaussianVerticalFold L r) := by
  have hnum := SmallRadiusQuantile.small_radius_quantile hr hsmall
  have hp : intervalMass r ∈ Ioo (0 : ℝ) 1 := hnum.1
  have hτ : Φ (q (intervalMass r)) < (1 : ℝ)/2 := by
    rw [Φ_q hp]
    have hh := SmallRadiusQuantile.intervalMass_le_radius hr.le
    change intervalMass r ≤ r at hh
    linarith
  have hsection' : PlanarSupport.horizontalSection L (q (intervalMass r)) = Iic a := by
    simpa only [PlanarSupport.horizontalSection, PlanarCap.horizontalSection,
      ← point_eq_support] using hSection
  obtain ⟨c, s, hc, hs, hunit, _, hSupport⟩ :=
    PlanarSupport.exists_supporting_normal L hLc hLv
      (fun x hx z hz => hLower hx hz) hMass (q (intervalMass r)) a hτ hsection'
  by_cases hs0 : s = 0
  · have hsubset : L ⊆ gaussianVerticalFold L r := by
      intro z hz
      rw [fold_eq_translate_inter L hLc hLower hr.le hp a hSection]
      refine ⟨?_, ?_⟩
      · rw [mem_translate]
        apply hLower hz
        intro i
        fin_cases i
        · simp [PlanarCap.point]
        · change z 1-r ≤ z 1
          linarith
      · have hh := hSupport z hz
        have hmul : c*z 0 ≤ c*a := by simpa only [hs0, zero_mul, add_zero] using hh
        exact (mul_le_mul_iff_right₀ hc).mp hmul
    exact measureReal_mono hsubset
  · exact gaussian_mass_fold_ge_of_support L hLc hLv hLower hMass r hr hsmall a c s hc
      (lt_of_le_of_ne hs (Ne.symm hs0)) hunit hSection hSupport

end OAI.GaussianPropeller.PlanarFoldComparison
