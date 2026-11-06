import Tusnady.TestFunctionL2
import Tusnady.CellFamilyL2
import Tusnady.PrimitiveL2

/-! Exact reindexing between W's block labels and the physical shape families. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace Tusnady.Witness
variable {d h : ℕ} {j : Fin d}

def physicalShapes (S : Finset (BlockShape j h)) : Finset (Dyadic.Shape d h) :=
  S.image (blockShapeEquiv j)

def physicalShapesEquiv (S : Finset (BlockShape j h)) : S ≃ physicalShapes S :=
  Equiv.subtypeEquiv (blockShapeEquiv j) (by
    intro r
    simp [physicalShapes])

/-- Actual bijection of all cell choices, including incompatible ones. -/
def physicalChoicesEquiv (S : Finset (BlockShape j h)) :
    CellChoice S ≃ Cell.Family (physicalShapes S) :=
  Equiv.piCongr (physicalShapesEquiv S) (fun _ => Equiv.refl _)

lemma physicalShapes_nonempty (S : Finset (BlockShape j h)) (hS : S.Nonempty) :
    (physicalShapes S).Nonempty := Finset.Nonempty.image hS _

lemma chosenSet_distinctShapes (S : Finset (BlockShape j h)) (c : CellChoice S) :
    Set.InjOn (fun R : Shell d h => R.1) (↑(chosenSet S c)) := by
  intro R hR R' hR' hshape
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hR
  obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hR'
  have hrs : r = s := by
    apply Subtype.ext
    exact (blockShapeEquiv j).injective hshape
  subst s
  rfl

lemma physicalChoices_apply (S : Finset (BlockShape j h)) (c : CellChoice S) (r : S) :
    physicalChoicesEquiv S c (physicalShapesEquiv S r) = c r :=
  Equiv.piCongr_apply_apply _ _ c r

/-- The cell product occurring in W is exactly the physical family
product used by the proved cell-location theorem. -/
theorem cellFunction_eq_physicalFamily (S : Finset (BlockShape j h)) (c : CellChoice S)
    (x : Point d) :
    cellFunction S c x = Cell.familyProduct (physicalShapes S) (physicalChoicesEquiv S c) x := by
  rw [cellFunction, prod_chosenSet]
  unfold Cell.familyProduct
  rw [← (physicalShapesEquiv S).prod_comp
    (fun r => qShell (Cell.familyShell (physicalShapes S) (physicalChoicesEquiv S c) r) x)]
  apply Finset.prod_congr rfl
  intro r _
  unfold Cell.familyShell chosenShell
  rw [physicalChoices_apply]
  rfl

end Tusnady.Witness

namespace Tusnady.Witness
open MeasureTheory Set
open scoped BigOperators
variable {d h : ℕ} {j : Fin d}

/-- Reindexing the actual finite block fiber preserves its exact size. -/
theorem physicalShapes_fiber_card (S : Finset (BlockShape j h)) (a : BlockIndex h) :
    ((physicalShapes S).filter (fun r => r.depth j = a.val.val)).card =
      (FiniteBlocks.fiber S a).card := by
  classical
  symm
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    have hmem : (⟨a,r⟩ : BlockShape j h) ∈ S := by simpa [FiniteBlocks.fiber] using hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨⟨a,r⟩,hmem,rfl⟩,r.property⟩
  · intro r _ s _ hrs
    exact Subtype.ext hrs
  · intro r hr
    obtain ⟨hrS,hrdepth⟩ := Finset.mem_filter.mp hr
    obtain ⟨⟨b,⟨s,hs⟩⟩,hmem,hrs⟩ := Finset.mem_image.mp hrS
    change s = r at hrs
    subst r
    have hba : b = a := Subtype.ext (Fin.ext (hs.symm.trans hrdepth))
    subst b
    refine ⟨⟨s,hrdepth⟩,?_,rfl⟩
    simpa [FiniteBlocks.fiber] using hmem

lemma shapeCoefficient_nonempty (theta : ℝ) (S : Finset (BlockShape j h))
    (hc : shapeCoefficient j theta S ≠ 0) : S.Nonempty := by
  classical
  by_contra hn
  have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  subst S
  exact hc (shapeCoefficient_even_eq_zero j theta ∅ (by simp))

/-- Actual nonzero coefficients force every occupied block to have odd
size, by the already proved tanh/Walsh coefficient parity. -/
lemma shapeCoefficient_fiber_odd (theta : ℝ) (S : Finset (BlockShape j h))
    (hc : shapeCoefficient j theta S ≠ 0) (a : BlockIndex h)
    (ha : (FiniteBlocks.fiber S a).Nonempty) : Odd (FiniteBlocks.fiber S a).card := by
  rcases Nat.even_or_odd (FiniteBlocks.fiber S a).card with he | ho
  · exact False.elim (hc (shapeCoefficient_eq_zero_of_even_fiber j theta S a
      (by simpa [activeBlocks] using ha.ne_empty) he))
  · exact ho

/-- The actual nonzero shape coefficient implies the modulation parity
required by cell location, in the distinguished block coordinate. -/
theorem physicalShapes_peak_modulated (theta : ℝ) (S : Finset (BlockShape j h))
    (hc : shapeCoefficient j theta S ≠ 0) : Cell.peakModulated (physicalShapes S) j = true := by
  classical
  have hS := physicalShapes_nonempty S (shapeCoefficient_nonempty theta S hc)
  apply Cell.peakModulated_eq_true (physicalShapes S) hS j
  intro depth hdepth
  obtain ⟨r,hr,hrdepth⟩ := hdepth
  let a : BlockIndex h :=
    ⟨⟨depth,by rw [← hrdepth]; exact Nat.lt_succ_of_le (Dyadic.depth_le_shell r j)⟩,
      by change 3 ∣ depth; exact hrdepth ▸ r.three_dvd_depth j⟩
  have ha : (FiniteBlocks.fiber S a).Nonempty := by
    apply Finset.card_pos.mp
    rw [← physicalShapes_fiber_card S a]
    apply Finset.card_pos.mpr
    exact ⟨r,Finset.mem_filter.mpr ⟨hr,hrdepth⟩⟩
  have ho := shapeCoefficient_fiber_odd theta S hc a ha
  rw [← physicalShapes_fiber_card S a] at ho
  exact ho

/-- Exact equality of the actual W cell L² class and the actual physical
family L² class; the proof checks the real representatives. -/
theorem cellL2Vector_eq_familyL2 (S : Finset (BlockShape j h)) (hS : S.Nonempty)
    (H : ℕ) (hj : ∀ k, Dyadic.join (physicalShapes S) k+2 < H) (c : CellChoice S) :
    cellL2Vector ⟨S,c⟩ = Cell.familyL2 (physicalShapes S) (physicalShapes_nonempty S hS) hj
      (physicalChoicesEquiv S c) := by
  apply Lp.ext
  filter_upwards [cellL2Vector_ae ⟨S,c⟩,
    Cell.familyL2_ae (physicalShapes S) (physicalShapes_nonempty S hS) hj (physicalChoicesEquiv S c)] with x hx hy
  rw [hx,hy]
  exact cellFunction_eq_physicalFamily S c x

/-- Exact reindexing of the actual primitive-high energies in W. -/
theorem cell_sum_energy_eq_physical (S : Finset (BlockShape j h)) (hS : S.Nonempty)
    (H : ℕ) (hj : ∀ k, Dyadic.join (physicalShapes S) k+2 < H) :
    (∑ c : CellChoice S, ‖Haar.primitiveHighCLM d H h (cellL2Vector ⟨S,c⟩)‖^2) =
      ∑ c : Cell.Family (physicalShapes S), Cell.familyEnergy (physicalShapes S)
        (physicalShapes_nonempty S hS) hj c := by
  calc
    _ = ∑ c : CellChoice S, Cell.familyEnergy (physicalShapes S)
        (physicalShapes_nonempty S hS) hj (physicalChoicesEquiv S c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [cellL2Vector_eq_familyL2 S hS H hj c,Haar.primitiveHighCLM_norm_sq]
      rfl
    _ = _ := (physicalChoicesEquiv S).sum_comp _

/-- Actual fixed-shape remainder energy bound for the distinguished
coordinate zero. Nonzero coefficient supplies all parity/nonemptiness
conditions; the finite Haar cap is chosen, not assumed. -/
theorem cell_sum_energy_bound {n : ℕ} (theta : ℝ)
    (S : Finset (BlockShape (0 : Fin (n+1)) h))
    (hc : shapeCoefficient 0 theta S ≠ 0) :
    (∑ c : CellChoice S,
      ‖Haar.primitiveHighCLM (n+1) (h+3*(n+1)) h (cellL2Vector ⟨S,c⟩)‖^2) ≤
      Cell.cellLocationConstant (n+1)*DyadicFunctions.dyadicLength h^2*
        DyadicFunctions.dyadicLength (Dyadic.excess (physicalShapes S))*
        ((Dyadic.excess (physicalShapes S)+1:ℕ):ℝ)^(2*n) := by
  have hS := shapeCoefficient_nonempty theta S hc
  rw [cell_sum_energy_eq_physical S hS (h+3*(n+1)) (Cell.join_cap _ (by omega))]
  simpa only [Nat.add_sub_cancel_right] using
    Cell.family_cell_location (physicalShapes S) (physicalShapes_nonempty S hS)
      (by omega : 0 < n+1) (Cell.join_cap _ (by omega)) (physicalShapes_peak_modulated theta S hc)

end Tusnady.Witness

namespace Tusnady.Witness
open MeasureTheory
open scoped BigOperators
variable {h : ℕ}

/-- Dimension-d version with all zero-coordinate and cap conditions
constructed internally. The only analytic trigger is a genuinely nonzero
coefficient of the actual W expansion. -/
theorem cell_sum_energy_bound_dim (d : ℕ) (hd : 0 < d) (theta : ℝ)
    (S : Finset (BlockShape (⟨0,hd⟩ : Fin d) h))
    (hc : shapeCoefficient ⟨0,hd⟩ theta S ≠ 0) :
    (∑ c : CellChoice S,
      ‖Haar.primitiveHighCLM d (h+3*d) h (cellL2Vector ⟨S,c⟩)‖^2) ≤
      Cell.cellLocationConstant d*DyadicFunctions.dyadicLength h^2*
        DyadicFunctions.dyadicLength (Dyadic.excess (physicalShapes S))*
        ((Dyadic.excess (physicalShapes S)+1:ℕ):ℝ)^(2*(d-1)) := by
  cases d with
  | zero => omega
  | succ n =>
    convert! cell_sum_energy_bound theta S hc using 1 <;>
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel_right]

end Tusnady.Witness
