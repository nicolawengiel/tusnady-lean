import Tusnady.SamplingPrimitiveInclusion
import Tusnady.FiniteSamplingAnalysis
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! The genuine finite sparse primitive Hilbert space in cube L².
Evaluation is defined only through its proved canonical finite expansion. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace Tusnady.SamplingSpace

lemma cubeMeasure_eq_product_restrict (d : ℕ) :
    Haar.cubeMeasure d = (productVolume d).restrict (unitCube d) := by
  have he : unitCube d = Set.pi Set.univ (fun _ : Fin d => Ico (0 : ℝ) 1) := by
    ext x
    simp [unitCube]
  rw [he]
  unfold Haar.cubeMeasure Haar.unitMeasure productVolume
  exact (Measure.restrict_pi_pi _ _).symm

theorem samplingAmbientMeasure_eq_cubeMeasure (d H : ℕ) :
    samplingAmbientMeasure d H = Haar.cubeMeasure d := by
  rw [samplingAmbientMeasure, cubeMeasure_eq_product_restrict]
  exact Measure.restrict_congr_set (samplingDomain_ae_cube d H)

abbrev CubeL2 (d : ℕ) := Lp ℝ 2 (Haar.cubeMeasure d)
abbrev SparseCoordinates (d H : ℕ) := EuclideanSpace ℝ (Fin (sparseDimension d H))

lemma ambientBasis_cube_memLp (d H : ℕ) (i : Fin (sparseDimension d H)) :
    MemLp (ambientBasis d H i) 2 (Haar.cubeMeasure d) := by
  rw [← samplingAmbientMeasure_eq_cubeMeasure d H]
  exact ambientBasis_memLp d H i

def sparseCubeBasis (d H : ℕ) (i : Fin (sparseDimension d H)) : CubeL2 d :=
  (ambientBasis_cube_memLp d H i).toLp (ambientBasis d H i)

lemma sparseCubeBasis_ae (d H : ℕ) (i : Fin (sparseDimension d H)) :
    sparseCubeBasis d H i =ᵐ[Haar.cubeMeasure d] ambientBasis d H i :=
  (ambientBasis_cube_memLp d H i).coeFn_toLp

def sparseCubeLinear (d H : ℕ) : SparseCoordinates d H →ₗ[ℝ] CubeL2 d :=
  (Fintype.linearCombination ℝ (sparseCubeBasis d H)).comp (WithLp.linearEquiv 2 ℝ _).toLinearMap

def sparseCubeSynthesis (d H : ℕ) : SparseCoordinates d H →L[ℝ] CubeL2 d :=
  (sparseCubeLinear d H).toContinuousLinearMap

lemma sparseCubeSynthesis_ae (d H : ℕ) (b : SparseCoordinates d H) :
    sparseCubeSynthesis d H b =ᵐ[Haar.cubeMeasure d]
      (fun x => ∑ i, b i * ambientBasis d H i x) := by
  classical
  have hs : ∀ S : Finset (Fin (sparseDimension d H)),
      (∑ i ∈ S, b i • sparseCubeBasis d H i : CubeL2 d) =ᵐ[Haar.cubeMeasure d]
        (fun x => ∑ i ∈ S, b i * ambientBasis d H i x) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using Lp.coeFn_zero ℝ 2 (Haar.cubeMeasure d)
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (b i • sparseCubeBasis d H i)
        (∑ k ∈ S, b k • sparseCubeBasis d H k), Lp.coeFn_smul (b i) (sparseCubeBasis d H i),
        sparseCubeBasis_ae d H i, ih] with x hadd hsmul hb hr
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hadd hsmul
      rw [hadd, hsmul, hb, hr]
  change (∑ i, b i • sparseCubeBasis d H i : CubeL2 d) =ᵐ[Haar.cubeMeasure d] _
  exact hs Finset.univ

theorem sparseCubeSynthesis_norm_sq (d H : ℕ) (b : SparseCoordinates d H) :
    ‖sparseCubeSynthesis d H b‖ ^ 2 = ‖b‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hi : (∫ x, inner ℝ ((sparseCubeSynthesis d H b) x) ((sparseCubeSynthesis d H b) x)
      ∂Haar.cubeMeasure d) =
      ∫ x, (∑ i, b i * ambientBasis d H i x) ^ 2 ∂Haar.cubeMeasure d := by
    apply integral_congr_ae
    filter_upwards [sparseCubeSynthesis_ae d H b] with x hx
    rw [hx]
    simp only [RCLike.inner_apply, conj_trivial, ← pow_two]
  rw [hi, ← samplingAmbientMeasure_eq_cubeMeasure d H,
    FiniteSamplingAnalysis.integral_combination_sq _ _ (ambientBasis_memLp d H)
      (ambientBasis_inner d H)]
  simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq b).symm

lemma sparseCubeSynthesis_injective (d H : ℕ) : Function.Injective (sparseCubeSynthesis d H) := by
  intro b c hbc
  have hn := sparseCubeSynthesis_norm_sq d H (b - c)
  rw [map_sub, hbc, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn.symm))

def sparseCubeSpace (d H : ℕ) : Submodule ℝ (CubeL2 d) := LinearMap.range (sparseCubeLinear d H)

instance sparseCubeSpace_finiteDimensional (d H : ℕ) :
    FiniteDimensional ℝ (sparseCubeSpace d H) := LinearMap.finiteDimensional_range _

def sparseCubeEquiv (d H : ℕ) : SparseCoordinates d H ≃ₗ[ℝ] sparseCubeSpace d H :=
  LinearEquiv.ofInjective (sparseCubeLinear d H) (sparseCubeSynthesis_injective d H)

def sparseCubeCoordinates (d H : ℕ) : sparseCubeSpace d H →L[ℝ] SparseCoordinates d H :=
  (sparseCubeEquiv d H).symm.toLinearMap.toContinuousLinearMap

def sparseCubeRepresentative (d H : ℕ) (v : sparseCubeSpace d H) (x : Fin d → ℝ) : ℝ :=
  ∑ i, sparseCubeCoordinates d H v i * ambientBasis d H i x

lemma sparseCubeCoordinates_norm_sq (d H : ℕ) (v : sparseCubeSpace d H) :
    ‖sparseCubeCoordinates d H v‖ ^ 2 = ‖v‖ ^ 2 := by
  have h := sparseCubeSynthesis_norm_sq d H (sparseCubeCoordinates d H v)
  have he : sparseCubeSynthesis d H (sparseCubeCoordinates d H v) = (v : CubeL2 d) := by
    exact congrArg Subtype.val ((sparseCubeEquiv d H).apply_symm_apply v)
  rw [he] at h
  exact h.symm

lemma sparseCubeRepresentative_ae (d H : ℕ) (v : sparseCubeSpace d H) :
    (v : CubeL2 d) =ᵐ[Haar.cubeMeasure d] sparseCubeRepresentative d H v := by
  have h := sparseCubeSynthesis_ae d H (sparseCubeCoordinates d H v)
  have he : sparseCubeSynthesis d H (sparseCubeCoordinates d H v) = (v : CubeL2 d) :=
    congrArg Subtype.val ((sparseCubeEquiv d H).apply_symm_apply v)
  rw [he] at h
  exact h

lemma mem_sparseCubeSpace_of_coefficients (d H : ℕ) (v : CubeL2 d)
    (a : Fin (sparseDimension d H) → ℝ)
    (ha : v =ᵐ[Haar.cubeMeasure d] (fun x => ∑ i, a i * ambientBasis d H i x)) :
    v ∈ sparseCubeSpace d H := by
  have he : sparseCubeSynthesis d H (WithLp.toLp 2 a) = v :=
    Lp.ext ((sparseCubeSynthesis_ae d H (WithLp.toLp 2 a)).trans ha.symm)
  exact ⟨WithLp.toLp 2 a, he⟩

lemma sparseCubeRepresentative_eq_coefficients (d H : ℕ) (v : sparseCubeSpace d H)
    (a : Fin (sparseDimension d H) → ℝ)
    (ha : (v : CubeL2 d) =ᵐ[Haar.cubeMeasure d]
      (fun x => ∑ i, a i * ambientBasis d H i x)) (x : Fin d → ℝ) :
    sparseCubeRepresentative d H v x = ∑ i, a i * ambientBasis d H i x := by
  have he : sparseCubeSynthesis d H (WithLp.toLp 2 a) = (v : CubeL2 d) :=
    Lp.ext ((sparseCubeSynthesis_ae d H (WithLp.toLp 2 a)).trans ha.symm)
  have hc : sparseCubeCoordinates d H v = WithLp.toLp 2 a := by
    apply sparseCubeSynthesis_injective d H
    exact (congrArg Subtype.val ((sparseCubeEquiv d H).apply_symm_apply v)).trans he.symm
  simp only [sparseCubeRepresentative, hc]
  rfl

end Tusnady.SamplingSpace
