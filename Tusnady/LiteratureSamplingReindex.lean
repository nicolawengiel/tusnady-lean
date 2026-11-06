import Tusnady.LiteratureSamplingFrameApprox
import Tusnady.FrameLTNumerics

/-! # Reindexing an actual selected frame into an unweighted sample

The hypotheses here are explicit bounds on an actual finite subset.
The final literature theorem discharges these with the proved LT selection.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace Tusnady.LiteratureSampling

/-- Enumerate precisely the selected finite indices, without changing multiplicities. -/
def selectedIndex {M : ℕ} (S : Finset (Fin M)) : Fin S.card → Fin M :=
  fun j => ((Fintype.equivFinOfCardEq (α := S) (by simp)).symm j).val

theorem sum_selectedIndex {M : ℕ} (S : Finset (Fin M)) (F : Fin M → ℝ) :
    (∑ j : Fin S.card, F (selectedIndex S j)) = ∑ j ∈ S, F j := by
  classical
  let e : S ≃ Fin S.card := Fintype.equivFinOfCardEq (by simp)
  calc
    (∑ j : Fin S.card, F (selectedIndex S j)) = ∑ j : S, F j :=
      e.symm.sum_comp (fun j : S => F j)
    _ = ∑ j ∈ S, F j := Finset.sum_coe_sort S F

/-- Actual subset energy estimates give the required average-of-squares
bounds after the exact finite reindexing. -/
theorem selected_average_bounds {X : Type*} {D M : ℕ}
    (u : Fin D → X → ℝ) (ξ : Fin M → X) (hD : 0 < D) (hM : 0 < M)
    (S : Finset (Fin M)) (C : ℝ) (hC : 0 < C)
    (hcardlow : D ≤ S.card) (hcardup : (S.card : ℝ) ≤ C * (D : ℝ))
    (henergy : ∀ w : Frame.Space D,
      25 * ((D : ℝ) / M) * ‖w‖ ^ 2 ≤ Frame.energy (nodeVector u ξ) S w ∧
      Frame.energy (nodeVector u ξ) S w ≤ C * ((D : ℝ) / M) * ‖w‖ ^ 2)
    (a : Fin D → ℝ) :
    (25 / C) * (∑ i, a i ^ 2) ≤
      (1 / (S.card : ℝ)) * ∑ j : Fin S.card, |∑ i, a i * u i (ξ (selectedIndex S j))| ^ 2 ∧
    (1 / (S.card : ℝ)) * ∑ j : Fin S.card, |∑ i, a i * u i (ξ (selectedIndex S j))| ^ 2 ≤
      C * (∑ i, a i ^ 2) := by
  classical
  let w : Frame.Space D := WithLp.toLp 2 a
  let q : ℝ := ∑ i, a i ^ 2
  let T : ℝ := ∑ j ∈ S, |∑ i, a i * u i (ξ j)| ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnorm : ‖w‖ ^ 2 = q := by
    simp only [w, q, EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  have hsam : Frame.energy (nodeVector u ξ) S w = T / (M : ℝ) := by
    rw [nodeVector_energy u ξ hM]
    change (1 / (M : ℝ)) * ∑ j ∈ S, (∑ i, a i * u i (ξ j)) ^ 2 =
      (∑ j ∈ S, |∑ i, a i * u i (ξ j)| ^ 2) / (M : ℝ)
    simp only [sq_abs]
    ring
  have hbounds := henergy w
  rw [hnorm, hsam] at hbounds
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hScard : 0 < S.card := hD.trans_le hcardlow
  have hmreal : (0 : ℝ) < S.card := by exact_mod_cast hScard
  have hDcardreal : (D : ℝ) ≤ S.card := by exact_mod_cast hcardlow
  have hlow : 25 * (D : ℝ) * q ≤ T := by
    have hh : (25 * (D : ℝ) * q) / M ≤ T / M := by
      convert hbounds.1 using 1
      ring
    exact (div_le_div_iff_of_pos_right hMreal).mp hh
  have hup : T ≤ C * (D : ℝ) * q := by
    have hh : T / M ≤ (C * (D : ℝ) * q) / M := by
      convert hbounds.2 using 1
      ring
    exact (div_le_div_iff_of_pos_right hMreal).mp hh
  have hlowscale : (25 / C) * (S.card : ℝ) ≤ 25 * (D : ℝ) := by
    have hh : (25 : ℝ) * (S.card : ℝ) / C ≤ 25 * D :=
      (div_le_iff₀ hC).mpr (by nlinarith [hcardup])
    convert hh using 1
    ring
  have hupscale : C * (D : ℝ) ≤ C * (S.card : ℝ) :=
    mul_le_mul_of_nonneg_left hDcardreal hC.le
  have hreindex := sum_selectedIndex S (fun j => |∑ i, a i * u i (ξ j)| ^ 2)
  rw [hreindex]
  simp only [one_div, ← div_eq_inv_mul]
  change (25 / C) * q ≤ T / (S.card : ℝ) ∧ T / (S.card : ℝ) ≤ C * q
  constructor
  · apply (le_div_iff₀ hmreal).mpr
    have hs := mul_le_mul_of_nonneg_right hlowscale hq
    nlinarith
  · apply (div_le_iff₀ hmreal).mpr
    have hs := mul_le_mul_of_nonneg_right hupscale hq
    nlinarith

end Tusnady.LiteratureSampling
