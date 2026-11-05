/-
Adapted from RealRooted/BorceaBranden/BoundarySpecialization.lean, revision
5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837, Apache-2.0.
Only zero-specialization lists and their actual block-evaluation transport
are extracted; no multiaffine stability theorem is presumed.
-/
import Tusnady.External.RealRooted.MultivariateStability
import Tusnady.External.RealRooted.Mathlib.Algebra.MvPolynomial.Specialize
noncomputable section
open Complex
namespace RealRooted
/-- Successively specialize the variables in `l` to zero. -/
def specializeZeroList {sigma : Type*} (l : List sigma)
    (P : MvPolynomial sigma ℂ) : MvPolynomial sigma ℂ :=
  l.foldl (fun Q i => MvPolynomial.specializeZero i Q) P

@[simp]
theorem specializeZeroList_nil {sigma : Type*} (P : MvPolynomial sigma ℂ) :
    specializeZeroList [] P = P :=
  rfl

@[simp]
theorem specializeZeroList_cons {sigma : Type*} (i : sigma) (l : List sigma)
    (P : MvPolynomial sigma ℂ) :
    specializeZeroList (i :: l) P =
      specializeZeroList l (MvPolynomial.specializeZero i P) :=
  rfl

@[simp]
theorem specializeZeroList_zero {sigma : Type*} (l : List sigma) :
    specializeZeroList l (0 : MvPolynomial sigma ℂ) = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [specializeZeroList_cons, ih]

/-- Evaluation after a list of zero specializations. -/
theorem eval_specializeZeroList {sigma : Type*} [DecidableEq sigma]
    (l : List sigma)
    (P : MvPolynomial sigma ℂ) (z : sigma → ℂ) :
    MvPolynomial.eval z (specializeZeroList l P) =
      MvPolynomial.eval (fun i => if i ∈ l then 0 else z i) P := by
  classical
  induction l generalizing P with
  | nil => simp
  | cons i l ih =>
      rw [specializeZeroList_cons, ih, MvPolynomial.eval_specializeZero]
      apply congrArg (fun w : sigma → ℂ => MvPolynomial.eval w P)
      funext j
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

/-- Block specialization from list specialization: if zero-specializing the variables in `l`,
which are exactly the right-block variables, gives a stable or zero polynomial, then so does
specializing the whole right block at zero. -/
theorem MvUpperHalfPlaneStableOrZero.specializeRight_zero_of_specializeZeroList
    {tau sigma : Type*} {P : MvPolynomial (Sum tau sigma) ℂ} (l : List (Sum tau sigma))
    (hl : ∀ j, j ∈ l ↔ j.isRight = true)
    (hQ : MvUpperHalfPlaneStableOrZero (specializeZeroList l P)) :
    MvUpperHalfPlaneStableOrZero
      (_root_.RealRooted.specializeRight (fun _ : sigma => 0) P) := by
  classical
  have hQeval (x : tau → ℂ) (y : sigma → ℂ) :
      MvPolynomial.eval (Sum.elim x y) (specializeZeroList l P) =
        MvPolynomial.eval (Sum.elim x (fun _ => 0)) P := by
    rw [eval_specializeZeroList]
    apply congrArg (fun w : Sum tau sigma → ℂ => MvPolynomial.eval w P)
    funext j
    cases j <;> simp [hl]
  by_cases hzero : _root_.RealRooted.specializeRight (fun _ : sigma => 0) P = 0
  · exact Or.inl hzero
  have hQne : specializeZeroList l P ≠ 0 := by
    intro hQzero
    obtain ⟨x, _hx, heval⟩ := exists_upperHalfPlane_eval_ne_zero hzero
    apply heval
    rw [eval_specializeRight, ← hQeval x (fun _ => I), hQzero]
    simp
  right
  intro x hx
  rw [eval_specializeRight, ← hQeval x (fun _ => I)]
  exact (hQ.resolve_left hQne) (Sum.elim x (fun _ => I)) fun j => by
    cases j with
    | inl i => exact hx i
    | inr _ => simp


end RealRooted
