import Tusnady.ConcreteRemainder
import Tusnady.TestResponse

/-! Literal B-transpose response of the actual test primitive. Its linear
part and its actual physical error are identified at every sample point. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace.ConcreteSample
variable {d h m : ℕ} {c L : ℝ}

lemma pointPrimitive_lowProjection_sum (Hhaar : ℕ) (f : Witness.CubeHilbert d)
    (p : Point d) (hp : p ∈ UnitCube d) :
    Haar.pointPrimitiveCLM d p (Haar.lowProjection d Hhaar h f) =
      ∑ T : Haar.lowCrossLabels d Hhaar h,
        inner ℝ (Haar.tensorL2 T.val) f * Haar.normalizedTensorPrimitiveValue T.val p := by
  classical
  rw [Haar.lowProjection, Haar.projectionFor_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [map_smul, Haar.pointPrimitiveCLM_eq_boxPrimitive d p hp,
    Haar.boxPrimitive_tensorL2 T.val p hp]
  rfl

lemma response_lowProjection (A : ConcreteSample d h m c L) (Hhaar : ℕ)
    (f : Witness.CubeHilbert d) :
    (A.response Hhaar).adjoint (WithLp.toLp 2 (fun k =>
      Haar.pointPrimitiveCLM d (A.nodes k) (Haar.lowProjection d Hhaar h f))) =
      (0 : Witness.ShellCoefficients d h) := by
  classical
  have he : WithLp.toLp 2 (fun k =>
      Haar.pointPrimitiveCLM d (A.nodes k) (Haar.lowProjection d Hhaar h f)) =
      ∑ T : Haar.lowCrossLabels d Hhaar h,
        inner ℝ (Haar.tensorL2 T.val) f • WithLp.toLp 2
          (fun k => Haar.normalizedTensorPrimitiveValue T.val (A.nodes k)) := by
    ext k
    rw [euclidean_sum_apply]
    simp only [PiLp.smul_apply, PiLp.toLp_apply, smul_eq_mul]
    exact pointPrimitive_lowProjection_sum Hhaar f (A.nodes k)
      (samplingDomain_subset_UnitCube (A.nodes k).property)
  rw [he, map_sum]
  apply Finset.sum_eq_zero
  intro T _
  rw [map_smul, A.response_adjoint_lowTensor Hhaar T.val (Finset.mem_filter.mp T.property).2,
    smul_zero]

def testResponse (A : ConcreteSample d h m c L) (j : Fin d) (theta : ℝ)
    (u : Witness.Shell d h → ℝ) : Witness.ShellCoefficients d h :=
  (A.response (h + 3 * d)).adjoint (WithLp.toLp 2
    (fun k => boxPrimitive (Witness.testFunction j theta u) (A.nodes k)))

def errorResponse (A : ConcreteSample d h m c L) (j : Fin d) (theta : ℝ)
    (u : Witness.Shell d h → ℝ) : Witness.ShellCoefficients d h :=
  (A.response (h + 3 * d)).adjoint (A.sampledRemainder j theta u)

lemma testResponse_continuous (A : ConcreteSample d h m c L) (j : Fin d) (theta : ℝ) :
    Continuous (A.testResponse j theta) := by
  apply (A.response (h + 3 * d)).adjoint.continuous.comp
  apply (PiLp.continuous_toLp 2 (fun _ : Fin m => ℝ)).comp
  apply continuous_pi
  intro k
  exact Witness.continuous_primitive_coefficients j theta (A.nodes k)
    (samplingDomain_subset_UnitCube (A.nodes k).property)

lemma errorResponse_continuous (A : ConcreteSample d h m c L) (hd : 0 < d)
    (j : Fin d) (theta : ℝ) : Continuous (A.errorResponse j theta) :=
  (A.response (h + 3 * d)).adjoint.continuous.comp (A.sampledRemainder_continuous hd j theta)

theorem testResponse_eq_linear_add_error (A : ConcreteSample d h m c L)
    (j : Fin d) (theta : ℝ) (u : Witness.Shell d h → ℝ) (R : Witness.Shell d h) :
    A.testResponse j theta u R =
      (A.targetScale * Witness.shellVolume h * Witness.linearCoefficient j theta R) * u R +
        A.errorResponse j theta u R := by
  let f := Witness.testL2 j theta u
  have hpoint : ∀ k, boxPrimitive (Witness.testFunction j theta u) (A.nodes k) =
      Witness.linearPrimitiveValue j theta u (A.nodes k) +
      Witness.physicalRemainder j theta u (A.nodes k) +
      Haar.pointPrimitiveCLM d (A.nodes k) (Haar.lowProjection d (h + 3 * d) h f) := by
    intro k
    have hp := samplingDomain_subset_UnitCube (A.nodes k).property
    have htotal := Haar.pointPrimitiveCLM_eq_boxPrimitive d (A.nodes k) hp f
    rw [Haar.boxPrimitive_congr_cube_ae _ _ (Witness.testL2_ae j theta u) (A.nodes k) hp] at htotal
    have hhigh := Haar.pointPrimitiveCLM_eq_boxPrimitive d (A.nodes k) hp
      (Haar.highProjection d (h + 3 * d) h f)
    rw [Haar.highProjection, map_sub] at hhigh
    change Haar.pointPrimitiveCLM d (A.nodes k) f -
      Haar.pointPrimitiveCLM d (A.nodes k) (Haar.lowProjection d (h + 3 * d) h f) =
      boxPrimitive (Haar.highProjection d (h + 3 * d) h f) (A.nodes k) at hhigh
    change _ = Witness.linearPrimitiveValue j theta u (A.nodes k) +
      (boxPrimitive (Haar.highProjection d (h + 3 * d) h f) (A.nodes k) -
        Witness.linearPrimitiveValue j theta u (A.nodes k)) + _
    linarith
  have he : WithLp.toLp 2 (fun k => boxPrimitive (Witness.testFunction j theta u) (A.nodes k)) =
      WithLp.toLp 2 (fun k => Witness.linearPrimitiveValue j theta u (A.nodes k)) +
        A.sampledRemainder j theta u +
        WithLp.toLp 2 (fun k => Haar.pointPrimitiveCLM d (A.nodes k)
          (Haar.lowProjection d (h + 3 * d) h f)) := by
    ext k
    exact hpoint k
  unfold testResponse errorResponse
  rw [he, map_add, map_add, A.response_lowProjection, add_zero]
  simp only [PiLp.add_apply, response_linearPrimitive]

def responseWeights (A : ConcreteSample d h m c L) (j : Fin d) (theta : ℝ)
    (R : Witness.Shell d h) : ℝ :=
  A.targetScale * Witness.shellVolume h * Witness.linearCoefficient j theta R

theorem testResponse_decomposition (A : ConcreteSample d h m c L)
    (j : Fin d) (theta : ℝ) (u : Witness.Shell d h → ℝ) :
    A.testResponse j theta u =
      WithLp.toLp 2 (fun R => A.responseWeights j theta R * u R) + A.errorResponse j theta u := by
  ext R
  exact A.testResponse_eq_linear_add_error j theta u R

lemma inner_testResponse (A : ConcreteSample d h m c L) (j : Fin d) (theta : ℝ)
    (u z : Witness.Shell d h → ℝ) :
    inner ℝ (WithLp.toLp 2 z : Witness.ShellCoefficients d h) (A.testResponse j theta u) =
      ∑ k, (A.responseMatrix (h + 3 * d)).mulVec z k *
        boxPrimitive (Witness.testFunction j theta u) (A.nodes k) := by
  unfold testResponse
  rw [ContinuousLinearMap.adjoint_inner_right, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← responseMatrix_mulVec]
  simp [RCLike.inner_apply, mul_comm]

theorem testResponse_weighted_duality {k : ℕ} (A : ConcreteSample (k + 1) h m c L)
    (j : Fin (k + 1)) (theta : ℝ) (u z : Witness.Shell (k + 1) h → ℝ)
    (hu : ∀ R, |u R| ≤ 1) (t : ℝ) (ht : 0 ≤ t)
    (hcount : ∀ x ∈ UnitCube (k + 1),
      |∑ i ∈ trace (fun l => (A.nodes l : Point (k + 1))) x,
        (A.responseMatrix (h + 3 * (k + 1))).mulVec z i| ≤ t) :
    inner ℝ (WithLp.toLp 2 z : Witness.ShellCoefficients (k + 1) h)
      (A.testResponse j theta u) ≤ t := by
  rw [inner_testResponse]
  apply (le_abs_self _).trans
  exact testFunction_weighted_duality j theta u hu (fun l => (A.nodes l : Point (k + 1)))
    (fun l => samplingDomain_subset_UnitCube (A.nodes l).property)
    ((A.responseMatrix (h + 3 * (k + 1))).mulVec z) t ht hcount

end Tusnady.SamplingSpace.ConcreteSample
