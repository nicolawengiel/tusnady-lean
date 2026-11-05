import Tusnady.PointMatrix
import Tusnady.GaussianSlabBody

/-! # The actual point-discrepancy Gaussian body

This specializes the Gaussian cover to the point incidence matrix. The
body's geometry, event interpretation, exponential probability and positive
conditioning mass are proved from actual point/matrix construction data.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal InnerProductSpace
namespace Tusnady

def pointGaussianBody {d n M : ℕ} (P : Fin n → Point d)
    (B : Matrix (Fin n) (Fin M) ℝ) (t : ℝ) : Set (Fin M → ℝ) :=
  gaussianSlabBody ((incidenceMatrix P).mulVecLin.comp B.mulVecLin) t

theorem mem_pointGaussianBody_iff {d n M : ℕ} (P : Fin n → Point d)
    (B : Matrix (Fin n) (Fin M) ℝ) (t : ℝ) (z : Fin M → ℝ) :
    z ∈ pointGaussianBody P B t ↔
      ∀ x : Point d, |∑ i ∈ trace P x, B.mulVec z i| ≤ t := by
  constructor
  · intro hz x
    obtain ⟨r, hr⟩ := incidenceRow_surjective P _ (trace_mem_traces P x)
    have h := hz r
    change |(incidenceMatrix P).mulVec (B.mulVec z) r| ≤ t at h
    rwa [incidenceMatrix_mulVec, hr] at h
  · intro hz r
    obtain ⟨x, hx⟩ := (mem_traces_iff P _).mp (incidenceRow_mem P r)
    change |(incidenceMatrix P).mulVec (B.mulVec z) r| ≤ t
    rw [incidenceMatrix_mulVec, ← hx]
    exact hz x

theorem trace_clamp {d n : ℕ} (P : Fin n → Point d)
    (hP : ∀ i, P i ∈ OpenUnitCube d) (x : Point d) :
    trace P (fun j => max 0 (min 1 (x j))) = trace P x := by
  classical
  ext i
  simp only [trace, Finset.mem_filter, Finset.mem_univ, true_and, Anchored, mem_setOf_eq]
  apply forall_congr'
  intro j
  constructor
  · intro h
    rcases le_max_iff.mp h with hz | hm
    · exact ((not_le.mpr (hP i j).1) hz).elim
    · exact hm.trans (min_le_right _ _)
  · intro h
    exact le_max_of_le_right (le_min (hP i j).2.le h)

/-- Exactly the manuscript's event, whose supremum runs over the unit
cube: no extra orthants have silently changed the body. -/
theorem mem_pointGaussianBody_iff_unitCube {d n M : ℕ} (P : Fin n → Point d)
    (hP : ∀ i, P i ∈ OpenUnitCube d)
    (B : Matrix (Fin n) (Fin M) ℝ) (t : ℝ) (z : Fin M → ℝ) :
    z ∈ pointGaussianBody P B t ↔
      ∀ x ∈ UnitCube d, |∑ i ∈ trace P x, B.mulVec z i| ≤ t := by
  rw [mem_pointGaussianBody_iff]
  constructor
  · exact fun h x _ => h x
  · intro h x
    have hc := h _ (clamp_mem_unitCube x)
    rwa [trace_clamp P hP x] at hc

theorem pointGaussianBody_isCompact {d n M : ℕ} (P : Fin n → Point d)
    (hP : Function.Injective P) (B : Matrix (Fin n) (Fin M) ℝ)
    (hB : Function.Injective B.mulVecLin) (t : ℝ) :
    IsCompact (pointGaussianBody P B t) := by
  apply gaussianSlabBody_isCompact
  intro z w h
  exact hB (incidenceMatrix_injective P hP h)

/-- Actual §7 probability and geometry from hereditary point discrepancy.
`C` is only the construction's size constant `n≤C M`. -/
theorem pointGaussianBody_facts {d n M : ℕ} (literature : Literature.Assumptions)
    (P : Fin n → Point d) (hP : Function.Injective P)
    (B : Matrix (Fin n) (Fin M) ℝ) (hBinj : Function.Injective B.mulVecLin)
    (hBrow : ∀ i : Fin n, ∑ j : Fin M, B i j ^ 2 ≤ 1)
    (C : ℝ) (hsize : (n : ℝ) ≤ C * M) :
    let D := MatrixDiscrepancy.hereditary (incidenceMatrix P)
    let K := pointGaussianBody P B (2 * D)
    IsCompact K ∧ Convex ℝ K ∧ (∀ z, z ∈ K ↔ -z ∈ K) ∧
      ENNReal.ofReal (Real.exp (-(gaussianCoverEntropyRate * C) * M)) ≤
        Literature.standardGaussian M K ∧ 0 < gaussianConditioningMass M K := by
  dsimp only
  exact ⟨pointGaussianBody_isCompact P hP B hBinj _, gaussianSlabBody_convex _ _,
    gaussianSlabBody_symmetric _ _,
    gaussianSlabBody_mass_exp_lower literature (incidenceMatrix P) B _ C le_rfl hBrow hsize,
    gaussianSlabBody_conditioningMass_pos literature (incidenceMatrix P) B _ le_rfl hBrow⟩

/-- The actual point-matrix version of Proposition 7.2's obstruction
step. Only response, duality and quadratic error construction obligations
remain; neither a Gaussian measure nor its mass is a free input. -/
theorem pointGaussianBody_obstruction {d n M : ℕ}
    (literature : Literature.Assumptions) (hM : 0 < M)
    (P : Fin n → Point d) (hP : Function.Injective P)
    (B : Matrix (Fin n) (Fin M) ℝ) (hBinj : Function.Injective B.mulVecLin)
    (hBrow : ∀ i : Fin n, ∑ j : Fin M, B i j ^ 2 ≤ 1)
    (C : ℝ) (hsize : (n : ℝ) ≤ C * M)
    (weight : Fin M → ℝ) (smin rho : ℝ) (hsmin : 0 ≤ smin) (hrho : 0 ≤ rho)
    (hweight : ∀ j, smin ≤ weight j)
    (V err : (Fin M → ℝ) → EuclideanSpace ℝ (Fin M)) (herrcont : Continuous err)
    (hresponse : ∀ u ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      V u = WithLp.toLp 2 (fun j => weight j * u j) + err u)
    (hdual : ∀ z ∈ pointGaussianBody P B
      (2 * MatrixDiscrepancy.hereditary (incidenceMatrix P)),
      ∀ u ∈ Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)),
      inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin M)) (V u) ≤
        2 * MatrixDiscrepancy.hereditary (incidenceMatrix P))
    (herr : (∫ u, ‖err u‖ ^ 2 ∂Measure.pi (fun _ : Fin M =>
      ProbabilityTheory.cond (volume : Measure ℝ) (Icc (-1 : ℝ) 1))) ≤
      (rho * smin) ^ 2 * M) :
    (gaussianRosenblattConstant (gaussianCoverEntropyRate * C) - rho) * smin * M ≤
      2 * MatrixDiscrepancy.hereditary (incidenceMatrix P) :=
  gaussianSlabBody_obstruction literature hM (incidenceMatrix P) B _ C le_rfl hBrow hsize
    ((incidenceMatrix_injective P hP).comp hBinj) weight smin rho hsmin hrho hweight
    V err herrcont hresponse hdual herr

end Tusnady
