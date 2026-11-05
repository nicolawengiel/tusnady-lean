import Tusnady.FrameBinaryEnergy
import Tusnady.FrameGram

/-!
# The actual r=2 tight-frame partition

The two equiprobable random vectors occupy orthogonal coordinate blocks.
The finite MSS realization is converted into simultaneous energy bounds
for the two complementary, actual subsets of the original frame.
-/
noncomputable section
open Matrix
open scoped BigOperators InnerProductSpace
namespace Tusnady.Frame

/-- Both parts of a tight frame obey the optimized MSS upper bound. -/
theorem exists_tight_partition {D M : ℕ} (v : Fin M → Space D) (hv : Tight v)
    {δ : ℝ} (hδ : 0 < δ) (hNorm : ∀ j, ‖v j‖ ^ 2 ≤ δ) :
    ∃ S : Finset (Fin M),
      (∀ w, energy v S w ≤ ((1 + Real.sqrt (2*δ))^2 / 2) * ‖w‖^2) ∧
      ∀ w, energy v (Finset.univ \ S) w ≤
        ((1 + Real.sqrt (2*δ))^2 / 2) * ‖w‖^2 := by
  classical
  have htrace (j : Fin M) :
      (RealRooted.MixedCharacteristic.secondMoment
        (binaryVector (fun i => v j i)) (fun _ : Bool => (1/2:ℝ))).trace ≤ 2*δ := by
    rw [binary_moment_trace]
    have hj := mul_le_mul_of_nonneg_left (hNorm j) (by norm_num : (0:ℝ) ≤ 2)
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using hj
  obtain ⟨s, _, hroots⟩ := FrameMSS.mss_roots_le
    (fun j => binaryVector (fun i => v j i)) (fun (_ : Fin M) (_ : Bool) => (1/2:ℝ))
    (fun _ _ => by norm_num) (fun _ => by norm_num [Fintype.sum_bool])
    (binary_moment_sum v (tight_gram v hv))
    (mul_pos (by norm_num : (0:ℝ) < 2) hδ) htrace
  let S := Finset.univ.filter (fun j => s j = false)
  have hcomp : Finset.univ \ S = Finset.univ.filter (fun j => s j = true) := by
    ext j
    cases hs : s j <;> simp [S, hs]
  refine ⟨S, ?_, ?_⟩
  · intro w
    have h := binary_energy_bound v s ((1+Real.sqrt (2*δ))^2) hroots false w
    change 2 * energy v S w ≤ _ at h
    nlinarith
  · intro w
    rw [hcomp]
    have h := binary_energy_bound v s ((1+Real.sqrt (2*δ))^2) hroots true w
    nlinarith

end Tusnady.Frame
