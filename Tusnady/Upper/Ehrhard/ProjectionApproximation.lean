import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Invertible diagonal approximation of coordinate projections

Retained coordinates have diagonal entry one; discarded coordinates have entry
`1/(n+1)`.  Every approximant is an actual continuous linear equivalence, with
an explicitly defined inverse.  The sequence converges on every vector to the
coordinate projection, including the zero projection and empty dimension.
These are algebraic and topological facts; no Gaussian premise is involved.
-/

namespace OAI.GaussianPropeller.CoordinateProjection

noncomputable section
open Filter
open scoped Topology

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

def scaleLinear (a : ι → ℝ) : E →ₗ[ℝ] E where
  toFun := fun x => WithLp.toLp 2 (fun i => a i * x i)
  map_add' := by intro x y; ext i; simp [mul_add]
  map_smul' := by intro r x; ext i; simp; ring

@[simp] theorem scaleLinear_apply (a : ι → ℝ) (x : E) (i : ι) :
    scaleLinear a x i = a i * x i := rfl

def scaleLinearEquiv (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) : E ≃ₗ[ℝ] E where
  toFun := scaleLinear a
  invFun := scaleLinear (fun i => (a i)⁻¹)
  left_inv := by intro x; ext i; simp [ha i]
  right_inv := by intro x; ext i; simp [ha i]
  map_add' := (scaleLinear a).map_add
  map_smul' := (scaleLinear a).map_smul

def scaleEquiv (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) : E ≃L[ℝ] E :=
  (scaleLinearEquiv a ha).toContinuousLinearEquiv

@[simp] theorem scaleEquiv_apply (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (x : E) (i : ι) :
    scaleEquiv a ha x i = a i * x i := rfl

@[simp] theorem scaleEquiv_symm_apply (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) (x : E) (i : ι) :
    (scaleEquiv a ha).symm x i = (a i)⁻¹ * x i := rfl

def projection (keep : ι → Bool) : E →L[ℝ] E :=
  (scaleLinear (fun i => if keep i then 1 else 0)).toContinuousLinearMap

@[simp] theorem projection_apply (keep : ι → Bool) (x : E) (i : ι) :
    projection keep x i = if keep i then x i else 0 := by
  change (if keep i then (1 : ℝ) else 0) * x i = _
  cases keep i <;> simp

def epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem epsilon_pos (n : ℕ) : 0 < epsilon n := by unfold epsilon; positivity

theorem epsilon_limit : Tendsto epsilon atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def coefficient (keep : ι → Bool) (n : ℕ) (i : ι) : ℝ :=
  if keep i then 1 else epsilon n

omit [Fintype ι] in
theorem coefficient_ne_zero (keep : ι → Bool) (n : ℕ) (i : ι) :
    coefficient keep n i ≠ 0 := by
  unfold coefficient
  cases keep i
  · exact (epsilon_pos n).ne'
  · norm_num

/-- Each matrix is invertible even if every coordinate is being discarded. -/
def approximant (keep : ι → Bool) (n : ℕ) : E ≃L[ℝ] E :=
  scaleEquiv (coefficient keep n) (coefficient_ne_zero keep n)

@[simp] theorem approximant_apply (keep : ι → Bool) (n : ℕ) (x : E) (i : ι) :
    approximant keep n x i = if keep i then x i else epsilon n * x i := by
  change coefficient keep n i * x i = _
  cases h : keep i <;> simp [coefficient, h]

/-- Pointwise convergence in the actual Euclidean topology. -/
theorem approximant_limit (keep : ι → Bool) (x : E) :
    Tendsto (fun n : ℕ => approximant keep n x) atTop (𝓝 (projection keep x)) := by
  have hpi : Tendsto (fun n : ℕ => fun i => coefficient keep n i * x i) atTop
      (𝓝 (fun i => if keep i then x i else 0)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    cases h : keep i
    · simpa only [coefficient, h, Bool.false_eq_true, ↓reduceIte, zero_mul] using
        epsilon_limit.mul_const (x i)
    · simpa only [coefficient, h, ↓reduceIte, one_mul] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => x i) atTop (𝓝 (x i)))
  have h := (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).continuousAt.tendsto.comp hpi
  have heq : WithLp.toLp 2 (fun i => if keep i then x i else 0) = projection keep x := by
    ext i
    simp
  simpa only [heq] using! h

/-- The exact existential interface for the linear-heat limiting theorem. -/
theorem exists_equiv_approximating_projection (keep : ι → Bool) :
    ∃ e : ℕ → E ≃L[ℝ] E, ∀ x : E,
      Tendsto (fun n : ℕ => e n x) atTop (𝓝 (projection keep x)) :=
  ⟨approximant keep, approximant_limit keep⟩

end
end OAI.GaussianPropeller.CoordinateProjection
