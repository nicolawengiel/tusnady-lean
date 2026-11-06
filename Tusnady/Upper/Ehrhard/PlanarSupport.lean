import Tusnady.Upper.Ehrhard.GaussianConvexOrigin
import Mathlib.Analysis.Convex.Topology

/-!
# A genuine supporting half-plane at a finite lower-set section endpoint

Strict separation of the open interior gives a nonzero supporting functional.
Coordinatewise lower closure forces nonnegative coefficients. Positive Gaussian
mass above the cutoff excludes a horizontal supporting line.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Topology InnerProductSpace
namespace OAI.GaussianPropeller.PlanarSupport
open Quantile
local notation "E" => EuclideanSpace ℝ (Fin 2)

def point (x y : ℝ) : E := WithLp.toLp 2 ![x,y]

@[simp] lemma point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] lemma point_one (x y : ℝ) : point x y 1 = y := rfl

lemma continuous_point : Continuous (fun p : ℝ × ℝ => point p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · change Continuous (fun p : ℝ × ℝ => p.1)
    exact continuous_fst
  · change Continuous (fun p : ℝ × ℝ => p.2)
    exact continuous_snd

def horizontalSection (L : Set E) (τ : ℝ) : Set ℝ := {x | point x τ ∈ L}

/-- The point at the finite section endpoint has a normalized nonnegative
supporting normal, with a strictly positive first coefficient. -/
theorem exists_supporting_normal (L : Set E) (hLc : IsClosed L) (hLv : Convex ℝ L)
    (hLower : ∀ x ∈ L, ∀ z : E, (∀ i, z i ≤ x i) → z ∈ L)
    (hMass : (1:ℝ)/2 ≤ (gaussianMeasure (Fin 2)).real L)
    (τ a₀ : ℝ) (hτ : Φ τ < (1:ℝ)/2)
    (hSection : horizontalSection L τ = Iic a₀) :
    ∃ c s : ℝ, 0 < c ∧ 0 ≤ s ∧ c^2+s^2=1 ∧ 0 ≤ c*a₀+s*τ ∧
      ∀ z ∈ L, c*z 0+s*z 1 ≤ c*a₀+s*τ := by
  classical
  let p := point a₀ τ
  have hp : p ∈ L := by
    have : a₀ ∈ horizontalSection L τ := by
      rw [hSection]
      exact (show a₀ ≤ a₀ from le_rfl)
    exact this
  let U : Set E := {z | z 0 < a₀ ∧ z 1 < τ}
  have hUopen : IsOpen U :=
    (isOpen_lt (PiLp.continuous_apply 2 _ 0) continuous_const).inter
      (isOpen_lt (PiLp.continuous_apply 2 _ 1) continuous_const)
  have hUL : U ⊆ L := by
    intro z hz
    apply hLower p hp z
    intro i
    fin_cases i
    · exact hz.1.le
    · exact hz.2.le
  have hUint : point (a₀-1) (τ-1) ∈ interior L := by
    apply interior_maximal hUL hUopen
    constructor <;> simp only [point_zero, point_one] <;> linarith
  have hIntne : (interior L).Nonempty := ⟨_, hUint⟩
  have hpnot : p ∉ interior L := by
    intro hpint
    let V := (fun x : ℝ => point x τ) ⁻¹' interior L
    have hVopen : IsOpen V := isOpen_interior.preimage
      (continuous_point.comp (continuous_id.prodMk continuous_const))
    have hVsub : V ⊆ Iic a₀ := by
      intro x hx
      rw [← hSection]
      change point x τ ∈ L
      change point x τ ∈ interior L at hx
      exact interior_subset hx
    have hbad : a₀ ∈ interior (Iic a₀) := interior_maximal hVsub hVopen hpint
    simpa only [interior_Iic, mem_Iio, lt_self_iff_false] using hbad
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hLv.interior isOpen_interior hpnot
  have hfne : f ≠ 0 := by
    intro hfzero
    have h := hf _ hUint
    simp only [hfzero, ContinuousLinearMap.zero_apply, lt_self_iff_false] at h
  have hclosure : closure (interior L) = L := by
    rw [hLv.closure_interior_eq_closure_of_nonempty_interior hIntne, hLc.closure_eq]
  have hfsupport : ∀ z ∈ L, f z ≤ f p := by
    have hsub : closure (interior L) ⊆ {z | f z ≤ f p} :=
      closure_minimal (fun z hz => (hf z hz).le) (isClosed_le f.continuous continuous_const)
    intro z hz
    exact hsub (hclosure.symm ▸ hz)
  let u : E := (InnerProductSpace.toDual ℝ E).symm f
  have huf (z : E) : inner ℝ u z = f z := InnerProductSpace.toDual_symm_apply
  have hu : u ≠ 0 := by
    intro hzero
    apply hfne
    ext z
    rw [← huf z, hzero, inner_zero_left]
    rfl
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let v : E := (‖u‖)⁻¹ • u
  have hvnorm : ‖v‖ = 1 := by simp [v, norm_smul, hun.ne']
  have hvsupport : ∀ z ∈ L, inner ℝ v z ≤ inner ℝ v p := by
    intro z hz
    dsimp only [v]
    rw [real_inner_smul_left, real_inner_smul_left, huf, huf]
    exact mul_le_mul_of_nonneg_left (hfsupport z hz) (inv_pos.mpr hun).le
  have hvnonneg (i : Fin 2) : 0 ≤ v i := by
    let e := EuclideanSpace.basisFun (Fin 2) ℝ i
    have he (j : Fin 2) : 0 ≤ e j := by
      simp only [e, EuclideanSpace.basisFun_apply, EuclideanSpace.single_apply]
      split_ifs <;> norm_num
    have hq : p-e ∈ L := hLower p hp (p-e) (fun j => by simp only [PiLp.sub_apply]; linarith [he j])
    have h := hvsupport (p-e) hq
    rw [inner_sub_right, EuclideanSpace.inner_basisFun_real] at h
    linarith
  have hinner (z : E) : inner ℝ v z = v 0*z 0+v 1*z 1 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply', conj_trivial, Fin.sum_univ_two]
  have hunit : (v 0)^2+(v 1)^2=1 := by
    have h := EuclideanSpace.norm_sq_eq v
    rw [hvnorm] at h
    simpa only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, one_pow] using h.symm
  have hcpos : 0 < v 0 := by
    by_contra hc
    have hc0 : v 0 = 0 := le_antisymm (le_of_not_gt hc) (hvnonneg 0)
    have hs1 : v 1 = 1 := by nlinarith [hvnonneg 1]
    have hsub : L ⊆ {z : E | z 1 ≤ τ} := by
      intro z hz
      have h := hvsupport z hz
      simp only [hinner, hc0, hs1, zero_mul, one_mul, zero_add, p, point_one] at h
      exact h
    let e := EuclideanSpace.basisFun (Fin 2) ℝ 1
    have he : ‖e‖=1 := (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.norm_eq_one 1
    have hlaw : (gaussianMeasure (Fin 2)).map (fun z : E => z 1) = gaussianReal 0 1 := by
      have h := gaussianMeasure_inner_law e
      rw [he, one_pow, Real.toNNReal_one] at h
      simpa only [e, EuclideanSpace.basisFun_inner] using h
    have hm : (gaussianMeasure (Fin 2)).real {z : E | z 1 ≤ τ} = Φ τ := by
      have h := congrArg (fun μ : Measure ℝ => μ.real (Iic τ)) hlaw
      simp only [measureReal_def] at h
      rw [Measure.map_apply (by fun_prop) measurableSet_Iic] at h
      exact h.trans (Φ_eq_gaussianReal τ).symm
    have hbound := (measureReal_mono hsub).trans_eq hm
    linarith
  have hzero := closedConvex_zero_mem_of_half_gaussianMass L hLc hLv hMass
  have hD := hvsupport 0 hzero
  rw [inner_zero_right] at hD
  simp only [hinner, p, point_zero, point_one] at hD
  refine ⟨v 0, v 1, hcpos, hvnonneg 1, hunit, hD, ?_⟩
  intro z hz
  simpa only [hinner, p, point_zero, point_one] using hvsupport z hz

end OAI.GaussianPropeller.PlanarSupport
