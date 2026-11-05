import Tusnady.SamplingSpaceDetail
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual evaluation kernels and inverse Christoffel functions

Evaluation is performed only on the canonical pointwise representatives.
Its Riesz vector is explicitly synthesized from the proved affine basis.
The detail-space kernel is a genuine orthogonal difference, yielding the
Christoffel subtraction identity without assuming a basis formula.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace

/-- The explicit finite Riesz vector for point evaluation on V_j. -/
def evaluationKernel (j : ℕ) (t : ℝ) : L2Real :=
  l2Synthesis j (fun ib => basis j ib t)

theorem evaluationKernel_mem (j : ℕ) (t : ℝ) : evaluationKernel j t ∈ l2Space j := by
  rw [l2Space_eq_range]
  exact ⟨fun ib => basis j ib t, rfl⟩

theorem evaluationKernel_pairing_synthesis (j : ℕ) (t : ℝ) (a : BasisIndex j → ℝ) :
    inner ℝ (evaluationKernel j t) (l2Synthesis j a) = pointwiseSynthesis j a t := by
  have h := (basisL2_orthonormal j).inner_sum (fun ib => basis j ib t) a Finset.univ
  simpa only [evaluationKernel, l2Synthesis, Fintype.linearCombination_apply,
    conj_trivial, pointwiseSynthesis_apply, mul_comm] using h

/-- Evaluation of the canonical representative is the actual inner
product with its explicitly constructed Riesz vector. -/
theorem evaluationKernel_pairing (j : ℕ) (t : ℝ) (v : l2Space j) :
    inner ℝ (evaluationKernel j t) (v : L2Real) = canonicalRepresentative j v t := by
  have h := (Classical.choose_spec (existsUnique_l2_coefficients j v)).1
  rw [← h]
  exact evaluationKernel_pairing_synthesis j t (canonicalCoefficients j v)

theorem evaluationKernel_pairing_of_mem (j : ℕ) (t : ℝ) (v : L2Real) (hv : v ∈ l2Space j) :
    inner ℝ (evaluationKernel j t) v = canonicalRepresentative j ⟨v, hv⟩ t :=
  evaluationKernel_pairing j t ⟨v, hv⟩

theorem evaluationKernel_norm_sq (j : ℕ) (t : ℝ) :
    ‖evaluationKernel j t‖ ^ 2 = basisChristoffel j t := by
  rw [← real_inner_self_eq_norm_sq]
  have h := (basisL2_orthonormal j).inner_sum
    (fun ib => basis j ib t) (fun ib => basis j ib t) Finset.univ
  simpa only [evaluationKernel, l2Synthesis, Fintype.linearCombination_apply,
    conj_trivial, basisChristoffel, pow_two] using h

/-- Nested affine spaces assign exactly the same actual representative
to the same L² vector, including dyadic endpoints. -/
theorem canonicalRepresentative_nested {j k : ℕ} (hjk : j ≤ k) (v : l2Space j) :
    canonicalRepresentative j v =
      canonicalRepresentative k ⟨(v : L2Real), l2Space_mono hjk v.property⟩ := by
  apply canonicalRepresentative_unique
  · apply (mem_pointwiseSpace_iff k _).mp
    apply pointwiseSpace_mono hjk
    exact ⟨canonicalCoefficients j v, rfl⟩
  · exact canonicalRepresentative_ae j v

/-- The genuine orthogonal-difference kernel of evaluation on D_j. -/
def detailKernel : ℕ → ℝ → L2Real
  | 0, t => evaluationKernel 0 t
  | j + 1, t => evaluationKernel (j + 1) t - evaluationKernel j t

theorem detailKernel_mem (j : ℕ) (t : ℝ) : detailKernel j t ∈ detailSpace j := by
  cases j with
  | zero => exact evaluationKernel_mem 0 t
  | succ j =>
    constructor
    · intro w hw
      rw [real_inner_comm]
      change inner ℝ (evaluationKernel (j + 1) t - evaluationKernel j t) w = 0
      rw [inner_sub_left, evaluationKernel_pairing_of_mem (j + 1) t w (l2Space_mono (Nat.le_succ j) hw),
        evaluationKernel_pairing_of_mem j t w hw]
      have hcompat := canonicalRepresentative_nested (Nat.le_succ j) (⟨w, hw⟩ : l2Space j)
      rw [← congrFun hcompat t]
      ring
    · exact (l2Space (j + 1)).sub_mem (evaluationKernel_mem (j + 1) t)
        (l2Space_mono (Nat.le_succ j) (evaluationKernel_mem j t))

def detailRepresentative (j : ℕ) (v : detailSpace j) : ℝ → ℝ :=
  canonicalRepresentative j ⟨(v : L2Real), detailSpace_le_level j v.property⟩

theorem detailKernel_pairing (j : ℕ) (t : ℝ) (v : detailSpace j) :
    inner ℝ (detailKernel j t) (v : L2Real) = detailRepresentative j v t := by
  cases j with
  | zero => exact evaluationKernel_pairing 0 t v
  | succ j =>
    change inner ℝ (evaluationKernel (j + 1) t - evaluationKernel j t) (v : L2Real) = _
    rw [inner_sub_left, evaluationKernel_pairing_of_mem (j + 1) t (v : L2Real) v.property.2]
    have hz : inner ℝ (evaluationKernel j t) (v : L2Real) = 0 :=
      v.property.1 _ (evaluationKernel_mem j t)
    rw [hz, sub_zero]
    rfl

theorem detailRepresentative_ae (j : ℕ) (v : detailSpace j) :
    (v : L2Real) =ᵐ[volume] detailRepresentative j v :=
  canonicalRepresentative_ae j ⟨(v : L2Real), detailSpace_le_level j v.property⟩

theorem detailRepresentative_memLp (j : ℕ) (v : detailSpace j) :
    MemLp (detailRepresentative j v) 2 (volume : Measure ℝ) :=
  MemLp.ae_eq (detailRepresentative_ae j v) (Lp.memLp (v : L2Real))

/-- The inverse Christoffel function as the squared norm of the actual
evaluation Riesz vector on the detail space. -/
def detailChristoffel (j : ℕ) (t : ℝ) : ℝ := ‖detailKernel j t‖ ^ 2

/-- Any chosen orthonormal basis is represented by actual canonical
functions, not by arbitrary L² equivalence-class values. -/
def detailBasis (j : ℕ) (i : Fin (Module.finrank ℝ (detailSpace j))) : ℝ → ℝ :=
  detailRepresentative j (stdOrthonormalBasis ℝ (detailSpace j) i)

theorem detailBasis_memLp (j : ℕ) (i : Fin (Module.finrank ℝ (detailSpace j))) :
    MemLp (detailBasis j i) 2 (volume : Measure ℝ) :=
  detailRepresentative_memLp j _

/-- The canonical functions of the chosen orthonormal detail basis have
actual Lebesgue mixed integrals equal to the Kronecker delta. -/
theorem detailBasis_inner (j : ℕ) (i k : Fin (Module.finrank ℝ (detailSpace j))) :
    (∫ x, detailBasis j i x * detailBasis j k x) = if i = k then 1 else 0 := by
  have hstd := orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (detailSpace j)).orthonormal i k
  have hactual : inner ℝ
      ((stdOrthonormalBasis ℝ (detailSpace j) i : detailSpace j) : L2Real)
      ((stdOrthonormalBasis ℝ (detailSpace j) k : detailSpace j) : L2Real) =
      ∫ x, detailBasis j i x * detailBasis j k x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [detailRepresentative_ae j (stdOrthonormalBasis ℝ (detailSpace j) i),
      detailRepresentative_ae j (stdOrthonormalBasis ℝ (detailSpace j) k)] with x hi hk
    rw [hi, hk]
    simp only [RCLike.inner_apply, conj_trivial, detailBasis]
    ring
  exact hactual.symm.trans hstd

theorem detailBasis_measurable (j : ℕ) (i : Fin (Module.finrank ℝ (detailSpace j))) :
    Measurable (detailBasis j i) :=
  canonicalRepresentative_measurable j _

theorem detailBasis_product_integrable (j k : ℕ)
    (i : Fin (Module.finrank ℝ (detailSpace j)))
    (l : Fin (Module.finrank ℝ (detailSpace k))) :
    Integrable (fun x => detailBasis j i x * detailBasis k l x) :=
  (detailBasis_memLp j i).integrable_mul (detailBasis_memLp k l)

theorem detailBasis_inner_interlevel {j k : ℕ} (hjk : j ≠ k)
    (i : Fin (Module.finrank ℝ (detailSpace j)))
    (l : Fin (Module.finrank ℝ (detailSpace k))) :
    (∫ x, detailBasis j i x * detailBasis k l x) = 0 := by
  let f := stdOrthonormalBasis ℝ (detailSpace j) i
  let g := stdOrthonormalBasis ℝ (detailSpace k) l
  have hinner : inner ℝ (f : L2Real) (g : L2Real) = 0 := by
    rcases lt_or_gt_of_ne hjk with h | h
    · exact detailSpace_inner_zero h _ _ f.property g.property
    · rw [real_inner_comm]
      exact detailSpace_inner_zero h _ _ g.property f.property
  have hactual : inner ℝ (f : L2Real) (g : L2Real) =
      ∫ x, detailBasis j i x * detailBasis k l x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [detailRepresentative_ae j f, detailRepresentative_ae k g] with x hi hl
    rw [hi, hl]
    simp only [RCLike.inner_apply, conj_trivial, detailBasis]
    ring
  exact hactual.symm.trans hinner

/-- The kernel definition is exactly the sum of squared values of an
actual orthonormal basis, as required by the Christoffel definition. -/
theorem detailChristoffel_basis_sum (j : ℕ) (t : ℝ) :
    detailChristoffel j t = ∑ i, detailBasis j i t ^ 2 := by
  let v : detailSpace j := ⟨detailKernel j t, detailKernel_mem j t⟩
  have h := (stdOrthonormalBasis ℝ (detailSpace j)).sum_sq_inner_left v
  have hp : ∀ i, inner ℝ v (stdOrthonormalBasis ℝ (detailSpace j) i) = detailBasis j i t := by
    intro i
    exact detailKernel_pairing j t _
  simp only [hp] at h
  exact h.symm

theorem detailChristoffel_zero (t : ℝ) : detailChristoffel 0 t = basisChristoffel 0 t :=
  evaluationKernel_norm_sq 0 t

/-- Proven subtraction identity for actual nested affine spaces. -/
theorem detailChristoffel_succ (j : ℕ) (t : ℝ) :
    detailChristoffel (j + 1) t = basisChristoffel (j + 1) t - basisChristoffel j t := by
  have horth : inner ℝ (evaluationKernel j t) (detailKernel (j + 1) t) = 0 :=
    (detailKernel_mem (j + 1) t).1 _ (evaluationKernel_mem j t)
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (evaluationKernel j t) (detailKernel (j + 1) t) horth
  have hsum : evaluationKernel j t + detailKernel (j + 1) t = evaluationKernel (j + 1) t := by
    unfold detailKernel
    module
  rw [hsum] at hpy
  simp only [← pow_two, evaluationKernel_norm_sq] at hpy
  unfold detailChristoffel
  nlinarith [hpy]

end Tusnady.SamplingSpace
