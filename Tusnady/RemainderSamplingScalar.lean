import Tusnady.RemainderDensity

/-!
# The actual continuous scalar function for mixed sampling

Clamping to the cube gives a globally continuous representative of sqrt(w).
It agrees with the manuscript's sqrt(w) at every admissible sample point
and has the exact same squared integral on the cube.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Tusnady.Witness
variable {d h : ℕ}

def cubeClamp (p : Point d) : Point d := fun j => max 0 (min 1 (p j))

lemma cubeClamp_mem (p : Point d) : cubeClamp p ∈ UnitCube d := by
  intro j
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma cubeClamp_eq_self (p : Point d) (hp : p ∈ UnitCube d) : cubeClamp p = p := by
  funext j
  dsimp [cubeClamp]
  rw [min_eq_right (hp j).2, max_eq_right (hp j).1]

lemma continuous_cubeClamp : Continuous (cubeClamp : Point d → Point d) := by
  apply continuous_pi
  intro j
  exact continuous_const.max (continuous_const.min (continuous_apply j))

def remainderSamplingScalar (j : Fin d) (theta : ℝ) (p : Point d) : ℝ :=
  Real.sqrt (cubicEnergyDensity (h := h) j theta (cubeClamp p))

lemma continuous_remainderSamplingScalar (hd : 0<d) (j : Fin d) (theta : ℝ) :
    Continuous (remainderSamplingScalar (h := h) j theta) := by
  apply Real.continuous_sqrt.comp
  exact (cubicEnergyDensity_continuousOn hd j theta).comp_continuous
    continuous_cubeClamp cubeClamp_mem

lemma remainderSamplingScalar_sq (j : Fin d) (theta : ℝ) (p : Point d)
    (hp : p ∈ UnitCube d) :
    remainderSamplingScalar (h := h) j theta p ^ 2 = cubicEnergyDensity (h := h) j theta p := by
  rw [remainderSamplingScalar, cubeClamp_eq_self p hp]
  exact Real.sq_sqrt (cubicEnergyDensity_nonneg (h := h) j theta p)

lemma UnitCube_isCompact (d : ℕ) : IsCompact (UnitCube d) := by
  have heq : UnitCube d = Icc (fun _ : Fin d => (0:ℝ)) (fun _ => (1:ℝ)) := by
    ext p
    simp only [UnitCube, Set.mem_setOf_eq, Set.mem_Icc, Pi.le_def]
    exact forall_and
  rw [heq]
  exact isCompact_Icc

/-- Actual L2 integrability for any probability measure, since the
continuous clamped representative is globally bounded. -/
theorem remainderSamplingScalar_memLp (hd : 0<d) (j : Fin d) (theta : ℝ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ] :
    MemLp (remainderSamplingScalar (h := h) j theta) 2 μ := by
  have hw := Real.continuous_sqrt.comp_continuousOn (cubicEnergyDensity_continuousOn (h := h) hd j theta)
  obtain ⟨B,hB⟩ := ((UnitCube_isCompact d).image_of_continuousOn hw).isBounded.exists_norm_le
  apply MemLp.of_bound (continuous_remainderSamplingScalar hd j theta).measurable.aestronglyMeasurable B
  apply Filter.Eventually.of_forall
  intro p
  exact hB _ ⟨cubeClamp p, cubeClamp_mem p, rfl⟩

theorem integral_remainderSamplingScalar_sq (j : Fin d) (theta : ℝ) :
    (∫ p, remainderSamplingScalar (h := h) j theta p ^ 2 ∂Haar.cubeMeasure d) =
      ∫ p, cubicEnergyDensity (h := h) j theta p ∂Haar.cubeMeasure d := by
  apply integral_congr_ae
  filter_upwards [Haar.cubeMeasure_ae_UnitCube d] with p hp
  exact remainderSamplingScalar_sq j theta p hp

end Tusnady.Witness
