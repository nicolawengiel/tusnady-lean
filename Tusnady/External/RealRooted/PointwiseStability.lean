/-
Adapted from Per Alexandersson's RealRooted, revision
5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837 (Apache-2.0; LICENSE in this directory).
Sources: RealRooted/LiebSokalPointwise.lean and RealRooted/LiebSokalBoundary.lean.
This is a deliberately narrow extraction of the logarithmic derivative and
one-minus-partial-derivative preservation proofs, adapted to Lean/mathlib 4.24.
-/
import Tusnady.External.RealRooted.MultivariateStability
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

noncomputable section
namespace RealRooted

/-- The logarithmic derivative of a nonconstant polynomial with no roots in
the open upper half-plane has strictly negative imaginary part there. -/
theorem _root_.Polynomial.derivative_eval_div_eval_im_neg
    (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0)
    (hdegree : p.natDegree ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    (p.derivative.eval z / p.eval z).im < 0 := by
  have hpz : p.eval z ≠ 0 := hp z hz
  have hpne : p ≠ 0 := fun hzero => hpz (by simp [hzero])
  have hsplits : p.Splits (RingHom.id ℂ) := IsAlgClosed.splits p
  have hroots_ne : p.roots ≠ 0 := by
    intro hzero
    have hcard := Polynomial.splits_iff_card_roots.mp hsplits
    rw [hzero, Multiset.card_zero] at hcard
    exact hdegree hcard.symm
  have hroots_im : ∀ r ∈ p.roots, r.im ≤ 0 := by
    intro r hr
    exact le_of_not_gt fun hrpos => hp r hrpos ((Polynomial.mem_roots hpne).mp hr)
  let S : Multiset ℂ := p.roots.map fun r => 1 / (z - r)
  have hS_ne : S ≠ 0 := by simp [S, hroots_ne]
  have hS_im (u : ℂ) (hu : u ∈ S) : u.im < 0 := by
    simp only [S, Multiset.mem_map] at hu
    obtain ⟨r, hr, rfl⟩ := hu
    exact Complex.one_div_sub_im_neg ((hroots_im r hr).trans_lt hz)
  have hsum_im : S.sum.im < 0 := by
    have hmap : S.sum.im = (S.map fun u => u.im).sum := by
      simpa using map_multiset_sum Complex.imAddGroupHom S
    rw [hmap]
    simpa using Multiset.sum_lt_sum_of_nonempty hS_ne hS_im
  rw [Polynomial.eval_derivative_div_eval_of_ne_zero_of_splits hsplits hpz]
  exact hsum_im

/-- The logarithmic derivative of a polynomial with no roots in the open
upper half-plane has nonpositive imaginary part there. -/
theorem _root_.Polynomial.derivative_eval_div_eval_im_nonpos
    (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0)
    {z : ℂ} (hz : 0 < z.im) :
    (p.derivative.eval z / p.eval z).im ≤ 0 := by
  by_cases hdegree : p.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hdegree]
    simp
  exact (p.derivative_eval_div_eval_im_neg hp hdegree hz).le


/-- Subtracting the derivative preserves absence of roots in the open upper
half-plane. -/
theorem _root_.Polynomial.sub_derivative_upperHalfPlaneStable
    (p : Polynomial ℂ) (hp : ∀ z : ℂ, 0 < z.im → p.eval z ≠ 0) :
    ∀ z : ℂ, 0 < z.im → (p - p.derivative).eval z ≠ 0 := by
  intro z hz
  have hpz : p.eval z ≠ 0 := hp z hz
  by_cases hdegree : p.natDegree = 0
  · rw [Polynomial.derivative_of_natDegree_zero hdegree]
    simpa using hpz
  have hratio_im := p.derivative_eval_div_eval_im_neg hp hdegree hz
  intro hzero
  have heval : p.eval z = p.derivative.eval z :=
    sub_eq_zero.mp (by simpa only [Polynomial.eval_sub] using hzero)
  rw [(div_eq_one_iff_eq hpz).mpr heval.symm] at hratio_im
  simp at hratio_im

/-- Each coordinate logarithmic derivative of a stable multivariate
polynomial has nonpositive imaginary part in the upper half-plane. -/
theorem MvUpperHalfPlaneStable.eval_pderiv_div_eval_im_nonpos
    {σ : Type*} {P : MvPolynomial σ ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : σ)
    (z : σ → ℂ) (hz : ∀ j, 0 < (z j).im) :
    (MvPolynomial.eval z (MvPolynomial.pderiv i P) /
      MvPolynomial.eval z P).im ≤ 0 := by
  classical
  let p : Polynomial ℂ := affineLineRestriction
    (Function.update z i 0) (Function.update (0 : σ → ℂ) i 1) P
  have hp (t : ℂ) (ht : 0 < t.im) : p.eval t ≠ 0 := by
    dsimp [p]
    rw [eval_affineLineRestriction_coordinate]
    apply hP
    intro j
    by_cases hji : j = i
    · subst j
      simpa using ht
    · simp [hji, hz j]
  have hratio := Polynomial.derivative_eval_div_eval_im_nonpos p hp (hz i)
  dsimp [p] at hratio
  rw [affineLineRestriction_derivative_coordinate,
    eval_affineLineRestriction_coordinate,
    eval_affineLineRestriction_coordinate] at hratio
  simpa using hratio


/-- Apply `1 - ∂ᵢ` to a multivariate polynomial. -/
noncomputable def oneSubPderiv {R sigma : Type*} [CommRing R] (i : sigma)
    (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  P - MvPolynomial.pderiv i P

/-- Apply an ordered list of one-minus-partial-derivative operators. -/
noncomputable def oneSubPderivList {R sigma : Type*} [CommRing R] (l : List sigma)
    (P : MvPolynomial sigma R) : MvPolynomial sigma R :=
  l.foldl (fun Q i => oneSubPderiv i Q) P

@[simp] theorem oneSubPderivList_nil {R sigma : Type*} [CommRing R]
    (P : MvPolynomial sigma R) : oneSubPderivList [] P = P :=
  rfl

@[simp] theorem oneSubPderivList_cons {R sigma : Type*} [CommRing R]
    (i : sigma) (l : List sigma) (P : MvPolynomial sigma R) :
    oneSubPderivList (i :: l) P = oneSubPderivList l (oneSubPderiv i P) :=
  rfl


/-- Applying `1 - ∂ᵢ` preserves upper-half-plane stability in arbitrary
coordinate degree. -/
theorem MvUpperHalfPlaneStable.oneSubPderiv
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (i : sigma) :
    MvUpperHalfPlaneStable (oneSubPderiv i P) := by
  classical
  intro z hz
  let q : Polynomial ℂ :=
    affineLineRestriction (Function.update z i 0)
      (Function.update (0 : sigma → ℂ) i 1) P
  have hqstable : ∀ w : ℂ, 0 < w.im → q.eval w ≠ 0 := by
    intro w hw
    rw [show q.eval w = MvPolynomial.eval (Function.update z i w) P by
      exact eval_affineLineRestriction_coordinate z i P w]
    apply hP
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hw
    · rw [Function.update_of_ne hji]
      exact hz j
  have hq := Polynomial.sub_derivative_upperHalfPlaneStable q hqstable (z i) (hz i)
  have hqeval : q.eval (z i) = MvPolynomial.eval z P := by
    dsimp [q]
    rw [eval_affineLineRestriction_coordinate]
    simp
  have hqderiv : q.derivative.eval (z i) =
      MvPolynomial.eval z (MvPolynomial.pderiv i P) := by
    dsimp [q]
    rw [affineLineRestriction_derivative_coordinate,
      eval_affineLineRestriction_coordinate]
    simp
  change MvPolynomial.eval z (P - MvPolynomial.pderiv i P) ≠ 0
  rw [MvPolynomial.eval_sub]
  simpa only [Polynomial.eval_sub, hqeval, hqderiv] using hq


/-- Complexification commutes with one application of `1 - ∂ᵢ`. -/
@[simp] theorem complexifyMv_oneSubPderiv {sigma : Type*}
    (i : sigma) (P : MvPolynomial sigma ℝ) :
    complexifyMv (oneSubPderiv i P) =
      oneSubPderiv i (complexifyMv P) := by
  simp [complexifyMv, oneSubPderiv, MvPolynomial.pderiv_map]

/-- Complexification commutes with an ordered list of `1 - ∂ᵢ` operators. -/
@[simp] theorem complexifyMv_oneSubPderivList {sigma : Type*}
    (l : List sigma) (P : MvPolynomial sigma ℝ) :
    complexifyMv (oneSubPderivList l P) =
      oneSubPderivList l (complexifyMv P) := by
  induction l generalizing P with
  | nil => rfl
  | cons i l ih =>
      rw [oneSubPderivList_cons, oneSubPderivList_cons, ih,
        complexifyMv_oneSubPderiv]

/-- Strict upper-half-plane stability is preserved by an ordered list of
`1 - ∂ᵢ` operators. -/
theorem MvUpperHalfPlaneStable.oneSubPderivList
    {sigma : Type*} {P : MvPolynomial sigma ℂ}
    (hP : MvUpperHalfPlaneStable P) (l : List sigma) :
    MvUpperHalfPlaneStable (oneSubPderivList l P) := by
  induction l generalizing P with
  | nil => exact hP
  | cons i l ih => exact ih (hP.oneSubPderiv i)

/-- The real `1 - ∂ᵢ` operator preserves real stability in arbitrary coordinate
degree. -/
theorem MvRealStable.oneSubPderiv {sigma : Type*}
    {P : MvPolynomial sigma ℝ} (hP : MvRealStable P) (i : sigma) :
    MvRealStable (oneSubPderiv i P) := by
  unfold MvRealStable at hP ⊢
  rw [complexifyMv_oneSubPderiv]
  exact hP.oneSubPderiv i

/-- Ordered finite iteration of the real `1 - ∂ᵢ` operator preserves real
stability. Repeated coordinates are allowed. -/
theorem MvRealStable.oneSubPderivList {sigma : Type*}
    {P : MvPolynomial sigma ℝ} (hP : MvRealStable P) (l : List sigma) :
    MvRealStable (oneSubPderivList l P) := by
  unfold MvRealStable at hP ⊢
  rw [complexifyMv_oneSubPderivList]
  exact hP.oneSubPderivList l


end RealRooted
