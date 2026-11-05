import Tusnady.DepthSelection
import Tusnady.PointMatrix

/-!
# Final cardinality and logarithmic transfer

This proves the entire final transfer from a depth construction to the
EXACT stated lower bound, including the hereditary subset and exactly N
distinct points. The remaining depth-construction proof is an explicit
local input here; this file does not declare a main theorem or add a
literature assumption.
-/
noncomputable section
namespace Tusnady

/-- The final step of Main.pdf Theorem 1.1. Every point, coloring, box and
cardinality is carried through explicitly. The local construction premise
must still be supplied by the actual analytic construction. -/
theorem lower_bound_from_depth_construction (d : ℕ) (hd : 3 ≤ d)
    (c C : ℝ) (hc : 0<c) (hC : 0<C) (hmin : ℕ)
    (construction : ∀ h : ℕ, 0<h → 3 ∣ h → hmin ≤ h →
      ∃ n : ℕ, ∃ P : Fin n → Point d, Function.Injective P ∧
        (∀ i, P i ∈ OpenUnitCube d) ∧
        (n:ℝ) ≤ C*((h:ℝ)+1)^(d-1)*(2:ℝ)^h ∧
        c*Real.rpow ((h:ℝ)+1) ((d:ℝ)-1/2) ≤
          MatrixDiscrepancy.hereditary (incidenceMatrix P)) :
    ∃ c' : ℝ, 0<c' ∧ ∃ N0 : ℕ, 1≤N0 ∧ ∀ N : ℕ, N0≤N →
      c'*targetGrowth d N ≤ worstDiscrepancy d N := by
  let a : ℝ := 1/(4*Real.log 2)
  let e : ℝ := (d:ℝ)-1/2
  have ha : 0<a := by dsimp [a]; exact div_pos (by norm_num) (mul_pos (by norm_num) log_two_pos)
  have he : 0≤e := by dsimp [e]; have h := (show (3:ℝ)≤d by exact_mod_cast hd); linarith
  obtain ⟨N0,hN0,hdepth⟩ := admissible_depth_for_cardinality (d-1) hmin C hC
  refine ⟨c*a^e, mul_pos hc (Real.rpow_pos_of_pos ha e), N0, hN0, ?_⟩
  intro N hN
  obtain ⟨hpos,hthree,hlarge,hcard,hlog⟩ := hdepth N hN
  obtain ⟨n,P,hPi,hPc,hn,hdisc⟩ := construction (cardinalityDepth N) hpos hthree hlarge
  have hnN : n≤N := by exact_mod_cast hn.trans hcard
  have hlogN : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN0.trans hN)
  have hbase : a*Real.log (N:ℝ) ≤ (cardinalityDepth N:ℝ)+1 := by
    simpa only [a, div_eq_mul_inv, one_mul, mul_comm] using hlog
  have hscale : (c*a^e)*targetGrowth d N ≤
      c*Real.rpow ((cardinalityDepth N:ℝ)+1) ((d:ℝ)-1/2) := by
    change (c*a^e)*Real.rpow (Real.log (N:ℝ)) e ≤ c*Real.rpow ((cardinalityDepth N:ℝ)+1) e
    calc
      _ = c*(Real.rpow a e * Real.rpow (Real.log (N:ℝ)) e) := by
        change (c*Real.rpow a e)*Real.rpow (Real.log (N:ℝ)) e = _
        exact mul_assoc _ _ _
      _ = c*Real.rpow (a*Real.log (N:ℝ)) e :=
        congrArg (fun x : ℝ => c*x) (Real.mul_rpow (z := e) ha.le hlogN).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (mul_nonneg ha.le hlogN) hbase he) hc.le
  obtain ⟨k,hkn,Q,hQi,hQc,_,hQdisc⟩ := incidenceMatrix_hereditary_subset P hPi hPc
  have hQlower : ∀ χ : Fin k → Bool, ∃ x : Point d,
      x ∈ UnitCube d ∧ (c*a^e)*targetGrowth d N ≤ |anchoredCount Q χ x| := by
    intro χ
    obtain ⟨x,hx,hbound⟩ := hQdisc χ
    exact ⟨x,hx,hscale.trans (hdisc.trans hbound)⟩
  obtain ⟨Pfinal,hFinal,hFinalLower⟩ := padding_to_exact_cardinality
    (show 0<d by omega) Q hQi hQc hQlower (hkn.trans hnN)
  apply le_trans _ (pointDiscrepancy_le_worst Pfinal hFinal)
  apply (le_pointDiscrepancy_iff Pfinal _).mpr
  intro χ
  obtain ⟨x,_,hx⟩ := hFinalLower χ
  exact ⟨x,hx⟩

end Tusnady
