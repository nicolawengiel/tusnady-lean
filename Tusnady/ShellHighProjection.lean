import Tusnady.ShellHilbert
import Tusnady.CellFactorIntegrability
import Tusnady.TestFunctionL2

/-!
# Actual shell retention by the high Haar projection

Each qShell is a product of the explicit four-Haar Walsh factors, all at
level depth+2. Its tensor level is h+2*d, so the actual high projection
retains it. This ties the physical linear term to JΦ exactly.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.Witness
open MeasureTheory Set
open scoped BigOperators
variable {d h : ℕ}

def qShellVector (R : Shell d h) : CubeHilbert d :=
  (qShell_memLp R).toLp (qShell R)

lemma qShellVector_ae (R : Shell d h) : qShellVector R =ᵐ[Haar.cubeMeasure d] qShell R :=
  (qShell_memLp R).coeFn_toLp

def shellFactors (hd : 0 < d) (R : Shell d h) : Fin d → Cell.Factor (h+3*d) :=
  fun k => .walsh (R.1.depth k) (by have hk := Dyadic.depth_le_shell R.1 k; omega) (R.2 k) 1

lemma shellFactors_value (hd : 0 < d) (R : Shell d h) :
    Cell.tensorFactorValue (shellFactors hd R) = qShell R := by
  funext x
  unfold Cell.tensorFactorValue shellFactors qShell
  simp only [Cell.factorValue,one_mul]

lemma shellFactors_level (hd : 0 < d) (R : Shell d h) :
    Cell.tensorFactorLevel (shellFactors hd R) = (h:ℤ)+2*d := by
  unfold Cell.tensorFactorLevel shellFactors
  simp only [Cell.factorLevel,Nat.cast_add,Nat.cast_ofNat,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hs : (∑ k, (R.1.depth k:ℤ)) = (h:ℤ) := by exact_mod_cast R.1.sum_depth
  rw [hs]
  ring

lemma qShellVector_eq_tensorFactor (hd : 0 < d) (R : Shell d h) :
    qShellVector R = Cell.tensorFactorL2 (shellFactors hd R) := by
  apply Lp.ext
  filter_upwards [qShellVector_ae R,Cell.tensorFactorL2_ae (shellFactors hd R)] with x hq ht
  rw [hq,ht,shellFactors_value]

/-- The actual shell Walsh vector is retained exactly by Φ. -/
theorem highProjection_qShellVector (hd : 0 < d) (R : Shell d h) :
    Haar.highProjection d (h+3*d) h (qShellVector R) = qShellVector R := by
  rw [qShellVector_eq_tensorFactor hd R,Cell.highProjection_tensorFactor,shellFactors_level]
  rw [if_pos (by omega : (h:ℤ) ≤ (h:ℤ)+2*d)]

/-- Consequently JΦq_R=v*T_R as equality of genuine L² vectors. -/
theorem primitiveHighCLM_qShellVector (hd : 0 < d) (R : Shell d h) :
    Haar.primitiveHighCLM d (h+3*d) h (qShellVector R) = shellVolume h • shellPrimitiveVector R := by
  change Haar.primitiveCLM d (Haar.highProjection d (h+3*d) h (qShellVector R)) = _
  rw [highProjection_qShellVector hd R]
  apply Lp.ext
  filter_upwards [Haar.primitiveCLM_ae (qShellVector R),Haar.cubeMeasure_ae_UnitCube d,
    Lp.coeFn_smul (shellVolume h) (shellPrimitiveVector R),shellPrimitiveVector_ae R] with p hJ hp hs hT
  rw [hJ,Haar.boxPrimitive_congr_cube_ae _ _ (qShellVector_ae R) p hp,
    boxPrimitive_qShell_normalized R p hp,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hT]

/-- The actual singleton cell vector in W is the actual qShell vector. -/
lemma singleton_cellL2Vector_eq_qShellVector {j : Fin d} (r : BlockShape j h)
    (c : CellChoice ({r} : Finset (BlockShape j h))) :
    cellL2Vector ⟨{r},c⟩ = qShellVector (chosenShell {r} c ⟨r,Finset.mem_singleton_self r⟩) := by
  classical
  apply Lp.ext
  filter_upwards [cellL2Vector_ae ⟨{r},c⟩,
    qShellVector_ae (chosenShell {r} c ⟨r,Finset.mem_singleton_self r⟩)] with x hc hq
  rw [hc,hq,cellFunction,prod_chosenSet]
  apply Fintype.prod_unique

theorem primitiveHighCLM_singleton_cellL2Vector (hd : 0 < d) {j : Fin d} (r : BlockShape j h)
    (c : CellChoice ({r} : Finset (BlockShape j h))) :
    Haar.primitiveHighCLM d (h+3*d) h (cellL2Vector ⟨{r},c⟩) =
      shellVolume h • shellPrimitiveVector (chosenShell {r} c ⟨r,Finset.mem_singleton_self r⟩) := by
  rw [singleton_cellL2Vector_eq_qShellVector]
  exact primitiveHighCLM_qShellVector hd _

end Tusnady.Witness
