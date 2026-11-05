import Tusnady.PointGaussianBody
import Tusnady.UniformMonomial
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Exact reindexing from actual shell variables to Fin M

Finite enumeration preserves matrix row norms, linear injectivity,
Euclidean inner products, and the actual product-uniform error integral.
The final theorem applies the Fin-indexed Gaussian obstruction directly
to an arbitrary actual finite coefficient type.
-/
set_option autoImplicit false
noncomputable section
namespace Tusnady.FiniteReindex
open MeasureTheory Set
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def sourceCoeff (e : ι ≃ κ) : (κ → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e.symm

omit [Fintype ι] [Fintype κ] in
@[simp] theorem sourceCoeff_apply (e : ι ≃ κ) (u : κ → ℝ) (i : ι) :
    sourceCoeff e u i = u (e i) := by
  simp [sourceCoeff,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft]

def euclideanReindex (e : ι ≃ κ) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ κ :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem euclideanReindex_apply (e : ι ≃ κ) (x : EuclideanSpace ℝ ι) (k : κ) :
    euclideanReindex e x k = x (e.symm k) := rfl

@[simp] theorem euclideanReindex_toLp (e : ι ≃ κ) (x : ι → ℝ) :
    euclideanReindex e (WithLp.toLp 2 x) = WithLp.toLp 2 (fun k => x (e.symm k)) := rfl

omit [Fintype ι] [Fintype κ] in
lemma sourceCoeff_continuous (e : ι ≃ κ) : Continuous (sourceCoeff e) := by
  apply continuous_pi
  intro i
  simpa only [sourceCoeff_apply] using (continuous_apply (e i) : Continuous (fun u : κ → ℝ => u (e i)))

omit [Fintype ι] [Fintype κ] in
lemma sourceCoeff_mem_cube (e : ι ≃ κ) (u : κ → ℝ)
    (hu : u ∈ Icc (fun _ => (-1:ℝ)) (fun _ => (1:ℝ))) :
    sourceCoeff e u ∈ Icc (fun _ => (-1:ℝ)) (fun _ => (1:ℝ)) := by
  constructor
  · intro i
    simpa only [sourceCoeff_apply] using hu.1 (e i)
  · intro i
    simpa only [sourceCoeff_apply] using hu.2 (e i)

lemma sourceCoeff_measurePreserving (e : ι ≃ κ) :
    MeasurePreserving (sourceCoeff e) (UniformMonomial.cubeLaw κ) (UniformMonomial.cubeLaw ι) :=
  measurePreserving_piCongrLeft (fun _ : ι => UniformMonomial.scalarLaw) e.symm

/-- The actual uniform coefficient law is transported exactly, so neither
the error constant nor its normalization changes under enumeration. -/
theorem uniform_error_integral (e : ι ≃ κ) (err : (ι → ℝ) → EuclideanSpace ℝ ι) :
    (∫ u, ‖euclideanReindex e (err (sourceCoeff e u))‖^2 ∂UniformMonomial.cubeLaw κ) =
      ∫ u, ‖err u‖^2 ∂UniformMonomial.cubeLaw ι := by
  simp only [LinearIsometryEquiv.norm_map]
  exact (sourceCoeff_measurePreserving e).integral_comp' (fun u => ‖err u‖^2)

def columnReindex {n : ℕ} (e : ι ≃ κ) (B : Matrix (Fin n) ι ℝ) : Matrix (Fin n) κ ℝ :=
  fun i k => B i (e.symm k)

lemma columnReindex_row_sq {n : ℕ} (e : ι ≃ κ) (B : Matrix (Fin n) ι ℝ) (i : Fin n) :
    (∑ k, columnReindex e B i k^2) = ∑ r, B i r^2 :=
  e.symm.sum_comp (fun r => B i r^2)

lemma columnReindex_mulVec {n : ℕ} (e : ι ≃ κ) (B : Matrix (Fin n) ι ℝ) (z : κ → ℝ) :
    (columnReindex e B).mulVec z = B.mulVec (sourceCoeff e z) := by
  funext i
  unfold Matrix.mulVec dotProduct columnReindex
  simpa only [sourceCoeff_apply,Equiv.symm_apply_apply] using
    (e.sum_comp (fun k => B i (e.symm k)*z k)).symm

lemma columnReindex_injective {n : ℕ} (e : ι ≃ κ) (B : Matrix (Fin n) ι ℝ)
    (hB : Function.Injective B.mulVecLin) : Function.Injective (columnReindex e B).mulVecLin := by
  intro z w hzw
  apply (sourceCoeff e).injective
  apply hB
  change B.mulVec (sourceCoeff e z) = B.mulVec (sourceCoeff e w)
  rw [← columnReindex_mulVec,← columnReindex_mulVec]
  exact hzw

end Tusnady.FiniteReindex

namespace Tusnady
open MeasureTheory Set FiniteReindex
open scoped BigOperators

/-- The actual point Gaussian obstruction for an arbitrary finite
coefficient type, specialized internally to Fin(card ι). Matrix columns,
response weights, duality and the product-uniform error law are all
transported by the same canonical enumeration; no reindexing premise remains. -/
theorem pointGaussianBody_obstruction_fintype {ι : Type*} [Fintype ι] {d n : ℕ}
    (literature : Literature.Assumptions) (hM : 0 < Fintype.card ι)
    (P : Fin n → Point d) (hP : Function.Injective P) (hPcube : ∀ i, P i ∈ OpenUnitCube d)
    (B : Matrix (Fin n) ι ℝ) (hBinj : Function.Injective B.mulVecLin)
    (hBrow : ∀ i : Fin n, ∑ r : ι, B i r^2 ≤ 1)
    (C : ℝ) (hsize : (n:ℝ) ≤ C*Fintype.card ι)
    (weight : ι → ℝ) (smin rho : ℝ) (hsmin : 0 ≤ smin) (hrho : 0 ≤ rho)
    (hweight : ∀ r, smin ≤ weight r)
    (V err : (ι → ℝ) → EuclideanSpace ℝ ι) (herrcont : Continuous err)
    (hresponse : ∀ u ∈ Icc (fun _ => (-1:ℝ)) (fun _ => (1:ℝ)),
      V u = WithLp.toLp 2 (fun r => weight r*u r)+err u)
    (hdual : ∀ z : ι → ℝ,
      (∀ x ∈ UnitCube d, |∑ i ∈ trace P x, B.mulVec z i| ≤
        2*MatrixDiscrepancy.hereditary (incidenceMatrix P)) →
      ∀ u ∈ Icc (fun _ => (-1:ℝ)) (fun _ => (1:ℝ)),
      inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ ι) (V u) ≤
        2*MatrixDiscrepancy.hereditary (incidenceMatrix P))
    (herr : (∫ u, ‖err u‖^2 ∂UniformMonomial.cubeLaw ι) ≤
      (rho*smin)^2*Fintype.card ι) :
    (gaussianRosenblattConstant (gaussianCoverEntropyRate*C)-rho)*smin*Fintype.card ι ≤
      2*MatrixDiscrepancy.hereditary (incidenceMatrix P) := by
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let Bfin := columnReindex e B
  let weightfin : Fin (Fintype.card ι) → ℝ := fun r => weight (e.symm r)
  let Vfin : (Fin (Fintype.card ι) → ℝ) → EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    fun u => euclideanReindex e (V (sourceCoeff e u))
  let errfin : (Fin (Fintype.card ι) → ℝ) → EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    fun u => euclideanReindex e (err (sourceCoeff e u))
  apply pointGaussianBody_obstruction literature hM P hP Bfin (columnReindex_injective e B hBinj)
    (fun i => (columnReindex_row_sq e B i).trans_le (hBrow i)) C hsize
    weightfin smin rho hsmin hrho (fun r => hweight (e.symm r)) Vfin errfin
    ((euclideanReindex e).continuous.comp (herrcont.comp (sourceCoeff_continuous e)))
  · intro u hu
    change euclideanReindex e (V (sourceCoeff e u)) = _
    rw [hresponse _ (sourceCoeff_mem_cube e u hu),map_add]
    congr 1
    ext r
    simp only [euclideanReindex_apply,PiLp.toLp_apply,sourceCoeff_apply,Equiv.apply_symm_apply]
    rfl
  · intro z hz u hu
    have hzactual : ∀ x ∈ UnitCube d, |∑ i ∈ trace P x, B.mulVec (sourceCoeff e z) i| ≤
        2*MatrixDiscrepancy.hereditary (incidenceMatrix P) := by
      have ha := (mem_pointGaussianBody_iff_unitCube P hPcube Bfin _ z).1 hz
      simpa only [Bfin,columnReindex_mulVec] using ha
    have hd := hdual (sourceCoeff e z) hzactual (sourceCoeff e u) (sourceCoeff_mem_cube e u hu)
    have hzvec : euclideanReindex e (WithLp.toLp 2 (sourceCoeff e z)) =
        (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin (Fintype.card ι))) := by
      ext r
      simp only [euclideanReindex_apply,PiLp.toLp_apply,sourceCoeff_apply,Equiv.apply_symm_apply]
    change inner ℝ (WithLp.toLp 2 z : EuclideanSpace ℝ (Fin (Fintype.card ι)))
      (euclideanReindex e (V (sourceCoeff e u))) ≤ _
    rw [← hzvec,LinearIsometryEquiv.inner_map_map]
    exact hd
  · have heq := uniform_error_integral e err
    change (∫ u, ‖euclideanReindex e (err (sourceCoeff e u))‖^2
      ∂UniformMonomial.cubeLaw (Fin (Fintype.card ι))) ≤ _
    rw [heq]
    exact herr

end Tusnady

namespace Tusnady.FiniteReindex
variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- The actual number of sample rows is at least the number of coefficient
variables as soon as the constructed response matrix is injective. -/
theorem matrix_card_le_of_injective (B : Matrix (Fin n) ι ℝ)
    (hB : Function.Injective B.mulVecLin) : Fintype.card ι ≤ n := by
  have h := LinearMap.finrank_le_finrank_of_injective hB
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin] using h

end Tusnady.FiniteReindex
