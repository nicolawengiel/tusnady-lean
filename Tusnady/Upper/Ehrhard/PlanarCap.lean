import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

/-!
# Capping a planar lower convex set along a supporting line

The plane carries the actual Euclidean norm. A supporting line through
(a, tau) is filled below that height. The filled set is the Minkowski sum
of the original set and its supporting downward wedge; this proves convexity
and the stability needed for the ball-to-vertical-translation inclusion.
-/
noncomputable section
open Set
open scoped Pointwise RealInnerProductSpace
namespace OAI.GaussianPropeller.PlanarCap

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def point (x y : ℝ) : Plane := WithLp.toLp 2 (Fin.cases x (fun _ : Fin 1 => y))
@[simp] lemma point_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] lemma point_one (x y : ℝ) : point x y 1 = y := rfl

def normal (c s : ℝ) (x : Plane) : ℝ := c*x 0+s*x 1

def LowerClosed (L : Set Plane) : Prop :=
  ∀ ⦃x y : Plane⦄, x ∈ L → (∀ i, y i ≤ x i) → y ∈ L

def horizontalSection (L : Set Plane) (t : ℝ) : Set ℝ := {x | point x t ∈ L}

def wedge (c s : ℝ) : Set Plane := {δ | δ 1 ≤ 0 ∧ normal c s δ ≤ 0}

def cap (L : Set Plane) (c s a t : ℝ) : Set Plane :=
  L ∪ {x | x 1 ≤ t ∧ normal c s x ≤ c*a+s*t}

lemma normal_add (c s : ℝ) (x y : Plane) :
    normal c s (x+y) = normal c s x+normal c s y := by
  change c*(x 0+y 0)+s*(x 1+y 1) = (c*x 0+s*x 1)+(c*y 0+s*y 1)
  ring

lemma normal_sub (c s : ℝ) (x y : Plane) :
    normal c s (x-y) = normal c s x-normal c s y := by
  change c*(x 0-y 0)+s*(x 1-y 1) = (c*x 0+s*x 1)-(c*y 0+s*y 1)
  ring

@[simp] lemma normal_point (c s a t : ℝ) : normal c s (point a t) = c*a+s*t := rfl
@[simp] lemma normal_zero (c s : ℝ) : normal c s 0 = 0 := by simp [normal]

lemma anchor_mem_of_section (L : Set Plane) (a t : ℝ)
    (hsection : horizontalSection L t = Iic a) : point a t ∈ L := by
  have h : a ∈ horizontalSection L t := by rw [hsection]; exact (le_rfl : a ≤ a)
  exact h

lemma subset_cap (L : Set Plane) (c s a t : ℝ) : L ⊆ cap L c s a t := subset_union_left

lemma cap_above_iff (L : Set Plane) (c s a t : ℝ) (x : Plane) (hx : t < x 1) :
    x ∈ cap L c s a t ↔ x ∈ L := by
  simp [cap, not_le.mpr hx]

lemma isClosed_cap {L : Set Plane} (hL : IsClosed L) (c s a t : ℝ) :
    IsClosed (cap L c s a t) := by
  have hi (i : Fin 2) : Continuous (fun x : Plane => x i) :=
    PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i
  apply hL.union
  exact (isClosed_le (hi 1) continuous_const).inter
    (isClosed_le (((hi 0).const_smul c).add ((hi 1).const_smul s)) continuous_const)

lemma convex_wedge (c s : ℝ) : Convex ℝ (wedge c s) := by
  intro x hx y hy a b ha hb hab
  constructor
  · change a*x 1+b*y 1 ≤ 0
    nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hx.1, mul_nonpos_of_nonneg_of_nonpos hb hy.1]
  · change c*(a*x 0+b*y 0)+s*(a*x 1+b*y 1) ≤ 0
    have hhx := mul_nonpos_of_nonneg_of_nonpos ha hx.2
    have hhy := mul_nonpos_of_nonneg_of_nonpos hb hy.2
    dsimp only [normal] at hhx hhy
    nlinarith

/-- A downward displacement not crossing the supporting line stays in the cap. -/
lemma shifted_mem_cap {L : Set Plane} (hconv : Convex ℝ L) (hlower : LowerClosed L)
    (c s a t : ℝ) (hc : 0 < c) (hp : point a t ∈ L)
    (hsupport : ∀ x ∈ L, normal c s x ≤ c*a+s*t)
    (x δ : Plane) (hx : x ∈ L) (hδ : δ ∈ wedge c s) :
    x+δ ∈ cap L c s a t := by
  have hn : normal c s (x+δ) ≤ c*a+s*t := by
    rw [normal_add]
    linarith [hsupport x hx, hδ.2]
  by_cases hbelow : (x+δ) 1 ≤ t
  · exact Or.inr ⟨hbelow, hn⟩
  · apply Or.inl
    have hnew : t < x 1+δ 1 := by exact lt_of_not_ge hbelow
    have hden : 0 < x 1-t := by linarith [hδ.1]
    let θ : ℝ := -δ 1/(x 1-t)
    have hθ0 : 0 ≤ θ := div_nonneg (neg_nonneg.mpr hδ.1) hden.le
    have hθ1 : θ ≤ 1 := (div_le_iff₀ hden).mpr (by linarith)
    have hθ : θ*(x 1-t) = -δ 1 := by dsimp only [θ]; field_simp [hden.ne']
    let z : Plane := (1-θ) • x+θ • point a t
    have hz : z ∈ L := hconv hx hp (by linarith) hθ0 (by ring)
    have hzy : z 1 = (x+δ) 1 := by
      change (1-θ)*x 1+θ*t = x 1+δ 1
      nlinarith [hθ]
    have hb : s*(x 1-t) ≤ c*(a-x 0) := by
      have h := hsupport x hx
      dsimp only [normal] at h
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hb hθ0
    have hθs := congrArg (fun q : ℝ => s*q) hθ
    have hzx : (x+δ) 0 ≤ z 0 := by
      change x 0+δ 0 ≤ (1-θ)*x 0+θ*a
      have hmul : c*(x 0+δ 0) ≤ c*((1-θ)*x 0+θ*a) := by
        have hδn := hδ.2
        dsimp only [normal] at hδn
        dsimp only at hθs
        nlinarith
      exact (mul_le_mul_iff_right₀ hc).mp hmul
    apply hlower hz
    intro i
    fin_cases i
    · exact hzx
    · exact hzy.ge

/-- Filling below the support line is exactly adding its downward wedge. -/
lemma cap_eq_add_wedge {L : Set Plane} (hconv : Convex ℝ L) (hlower : LowerClosed L)
    (c s a t : ℝ) (hc : 0 < c) (hp : point a t ∈ L)
    (hsupport : ∀ x ∈ L, normal c s x ≤ c*a+s*t) :
    cap L c s a t = L+wedge c s := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact ⟨x, hx, 0, by simp [wedge], by simp⟩
    · have hδ : x-point a t ∈ wedge c s := by
        constructor
        · change x 1-t ≤ 0
          linarith [hx.1]
        · rw [normal_sub, normal_point]
          linarith [hx.2]
      exact ⟨point a t, hp, x-point a t, hδ, by abel⟩
  · rintro ⟨y, hy, δ, hδ, rfl⟩
    exact shifted_mem_cap hconv hlower c s a t hc hp hsupport y δ hy hδ

lemma convex_cap {L : Set Plane} (hconv : Convex ℝ L) (hlower : LowerClosed L)
    (c s a t : ℝ) (hc : 0 < c) (hp : point a t ∈ L)
    (hsupport : ∀ x ∈ L, normal c s x ≤ c*a+s*t) :
    Convex ℝ (cap L c s a t) := by
  rw [cap_eq_add_wedge hconv hlower c s a t hc hp hsupport]
  exact hconv.add (convex_wedge c s)

lemma cap_stable {L : Set Plane} (hconv : Convex ℝ L) (hlower : LowerClosed L)
    (c s a t : ℝ) (hc : 0 < c) (hp : point a t ∈ L)
    (hsupport : ∀ x ∈ L, normal c s x ≤ c*a+s*t)
    (x δ : Plane) (hx : x ∈ cap L c s a t) (hδ : δ ∈ wedge c s) :
    x+δ ∈ cap L c s a t := by
  rcases hx with hx | hx
  · exact shifted_mem_cap hconv hlower c s a t hc hp hsupport x δ hx hδ
  · apply Or.inr
    constructor
    · change x 1+δ 1 ≤ t
      linarith [hx.1, hδ.1]
    · rw [normal_add]
      linarith [hx.2, hδ.2]

lemma cap_support {L : Set Plane} (c s a t : ℝ)
    (hsupport : ∀ x ∈ L, normal c s x ≤ c*a+s*t)
    {x : Plane} (hx : x ∈ cap L c s a t) : normal c s x ≤ c*a+s*t := by
  rcases hx with hx | hx
  · exact hsupport x hx
  · exact hx.2

lemma norm_sq_plane (x : Plane) : ‖x‖^2 = (x 0)^2+(x 1)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

lemma coordinate_one_le_norm (x : Plane) : x 1 ≤ ‖x‖ := by
  have hs : |x 1|^2 ≤ ‖x‖^2 := by
    rw [sq_abs, norm_sq_plane]
    nlinarith [sq_nonneg (x 0)]
  exact (le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hs)

lemma normal_eq_inner (c s : ℝ) (x : Plane) :
    normal c s x = inner ℝ (point c s) x := by
  simp only [normal, PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply', conj_trivial,
    point_zero, point_one]

lemma norm_normal_unit (c s : ℝ) (hunit : c^2+s^2=1) : ‖point c s‖ = 1 := by
  have hh := norm_sq_plane (point c s)
  simp only [point_zero, point_one, hunit] at hh
  nlinarith [norm_nonneg (point c s)]

lemma normal_le_norm (c s : ℝ) (hunit : c^2+s^2=1) (x : Plane) :
    normal c s x ≤ ‖x‖ := by
  rw [normal_eq_inner]
  simpa only [norm_normal_unit c s hunit, one_mul] using real_inner_le_norm (point c s) x

/-- The actual Euclidean ball enlargement fits in the vertical translate.
This is the geometric inclusion in Szusterman's Appendix Claim 4.2. -/
theorem cap_add_closedBall_subset_translate {L : Set Plane}
    (hconv : Convex ℝ L) (hlower : LowerClosed L) (c s a t : ℝ)
    (hc : 0 < c) (_hs : 0 < s) (hunit : c^2+s^2=1)
    (hp : point a t ∈ L) (hsupport : ∀ x ∈ L, normal c s x ≤ c*a+s*t)
    {r : ℝ} (hr : 0 ≤ r) :
    cap L c s a t + Metric.closedBall (0 : Plane) (r*s) ⊆
      cap L c s a t + ({point 0 r} : Set Plane) := by
  rintro z ⟨x, hx, v, hv, rfl⟩
  have hvnorm : ‖v‖ ≤ r*s := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg c, sq_nonneg (s-1)]
  have hradius : r*s ≤ r := mul_le_of_le_one_right hr hs1
  have hvheight : v 1 ≤ r := (coordinate_one_le_norm v).trans (hvnorm.trans hradius)
  have hδ : v-point 0 r ∈ wedge c s := by
    constructor
    · change v 1-r ≤ 0
      linarith
    · rw [normal_sub, normal_point]
      simp only [mul_zero, zero_add]
      nlinarith [normal_le_norm c s hunit v]
  have hxδ := cap_stable hconv hlower c s a t hc hp hsupport x (v-point 0 r) hx hδ
  exact ⟨x+(v-point 0 r), hxδ, point 0 r, mem_singleton _, by abel⟩

end OAI.GaussianPropeller.PlanarCap
