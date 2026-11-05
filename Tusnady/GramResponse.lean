import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# Actual Hilbert-space Gram inversion and exact response

All norms here are Hilbert norms or continuous-linear operator norms.
No norm on bare matrices is used. The lower sampling input is the actual
coercive norm inequality for the projected sampling map.

The low sampling space is a genuine submodule. Its orthogonal-complement
projection, Gram operator, inverse and response map are constructed, and
the response and annihilation conclusions are proved.
-/

noncomputable section
open scoped InnerProduct
namespace Tusnady.GramResponse

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The genuine orthogonal projector onto the complement of the low
sampling space. Finite dimensionality ensures this projector exists. -/
def highProjection (L : Submodule ℝ F) : F →L[ℝ] F := Lᗮ.starProjection

def gram (L : Submodule ℝ F) (T : E →L[ℝ] F) : E →L[ℝ] E :=
  T.adjoint.comp ((highProjection L).comp T)

theorem highProjection_mem (L : Submodule ℝ F) (z : F) :
    highProjection L z ∈ Lᗮ := (Lᗮ).starProjection_apply_mem z

theorem highProjection_norm_le (L : Submodule ℝ F) (z : F) :
    ‖highProjection L z‖ ≤ ‖z‖ := (Lᗮ).norm_starProjection_apply_le z

theorem highProjection_idempotent (L : Submodule ℝ F) (z : F) :
    highProjection L (highProjection L z) = highProjection L z :=
  Submodule.starProjection_eq_self_iff.mpr (highProjection_mem L z)

theorem highProjection_annihilates_low (L : Submodule ℝ F) (z : F)
    (w : F) (hw : w ∈ L) : inner ℝ w (highProjection L z) = 0 :=
  (highProjection_mem L z) w hw

/-- The Gram quadratic form is exactly the squared Hilbert norm of the
projected sampling vector. -/
theorem gram_energy (L : Submodule ℝ F) (T : E →L[ℝ] F) (x : E) :
    inner ℝ (gram L T x) x = ‖highProjection L (T x)‖ ^ 2 := by
  change inner ℝ (T.adjoint (highProjection L (T x))) x = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (Lᗮ).re_inner_starProjection_eq_normSq (T x)

/-- Positivity of the actual projected sampling energy makes the Gram
operator injective. This is the only coercivity input to the inverse. -/
theorem gram_injective (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2) :
    Function.Injective (gram L T) := by
  intro x y hxy
  have hzero : gram L T (x - y) = 0 := by simp [hxy]
  have he := gram_energy L T (x - y)
  rw [hzero, inner_zero_left] at he
  have hb := hsampling (x - y)
  have hmul : c * ‖x - y‖ ^ 2 ≤ 0 := hb.trans_eq he.symm
  have hsq : ‖x - y‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by simpa using hmul)
  have hnorm : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Finite-dimensional Gram equivalence constructed from the proved
injectivity; surjectivity is not an extra input. -/
def gramEquiv (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2) : E ≃L[ℝ] E :=
  (LinearEquiv.ofInjectiveEndo (gram L T).toLinearMap
    (gram_injective L T c hc hsampling)).toContinuousLinearEquiv

/-- The actual continuous inverse of the Gram operator. -/
def gramInverse (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2) : E →L[ℝ] E :=
  (gramEquiv L T c hc hsampling).symm.toContinuousLinearMap

theorem gram_gramInverse (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2) (x : E) :
    gram L T (gramInverse L T c hc hsampling x) = x :=
  (gramEquiv L T c hc hsampling).apply_symm_apply x

theorem gramInverse_gram (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2) (x : E) :
    gramInverse L T c hc hsampling (gram L T x) = x :=
  (gramEquiv L T c hc hsampling).symm_apply_apply x

/-- The response map is constructed as `Π T G⁻¹ S`. `S` can in particular
be the diagonal shell-response operator; it is not a response hypothesis. -/
def response (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) : E →L[ℝ] F :=
  (highProjection L).comp (T.comp ((gramInverse L T c hc hsampling).comp S))

/-- Exact response, proved by the actual inverse identity. -/
theorem adjoint_response (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    T.adjoint (response L T c hc hsampling S x) = S x :=
  gram_gramInverse L T c hc hsampling (S x)

theorem response_mem_high (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) : response L T c hc hsampling S x ∈ Lᗮ :=
  highProjection_mem L _

/-- Every low sample vector is annihilated exactly. -/
theorem response_annihilates_low (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) (w : F) (hw : w ∈ L) :
    inner ℝ w (response L T c hc hsampling S x) = 0 :=
  (response_mem_high L T c hc hsampling S x) w hw

/-- The actual inverse has the quantitative coercivity bound. -/
theorem gramInverse_norm_le (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2) (y : E) :
    ‖gramInverse L T c hc hsampling y‖ ≤ ‖y‖ / c := by
  let u := gramInverse L T c hc hsampling y
  have henergy : c * ‖u‖ ^ 2 ≤ inner ℝ y u := by
    have h := hsampling u
    rw [← gram_energy L T u, gram_gramInverse L T c hc hsampling y] at h
    exact h
  have hmul : (‖u‖ * c) * ‖u‖ ≤ ‖y‖ * ‖u‖ := by
    calc
      (‖u‖ * c) * ‖u‖ = c * ‖u‖ ^ 2 := by ring
      _ ≤ inner ℝ y u := henergy
      _ ≤ ‖y‖ * ‖u‖ := real_inner_le_norm _ _
  by_cases hu : ‖u‖ = 0
  · change ‖u‖ ≤ _
    rw [hu]
    exact div_nonneg (norm_nonneg _) hc.le
  · have hup : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
    exact (le_div_iff₀ hc).mpr ((mul_le_mul_iff_left₀ hup).mp hmul)

/-- Response energy without an unspecified bound on the constructed B. -/
theorem response_energy (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    ‖response L T c hc hsampling S x‖ ^ 2 =
      inner ℝ (S x) (gramInverse L T c hc hsampling (S x)) := by
  have h := gram_energy L T (gramInverse L T c hc hsampling (S x))
  rw [gram_gramInverse] at h
  exact h.symm

/-- Tight Hilbert-space square-norm bound for the constructed response. -/
theorem response_norm_sq_le (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    ‖response L T c hc hsampling S x‖ ^ 2 ≤ ‖S x‖ ^ 2 / c := by
  rw [response_energy]
  calc
    _ ≤ ‖S x‖ * ‖gramInverse L T c hc hsampling (S x)‖ := real_inner_le_norm _ _
    _ ≤ ‖S x‖ * (‖S x‖ / c) :=
      mul_le_mul_of_nonneg_left (gramInverse_norm_le L T c hc hsampling (S x)) (norm_nonneg _)
    _ = ‖S x‖ ^ 2 / c := by ring

/-- Choosing the diagonal scale within the sampling coercivity gives a
contraction. This is proved for the constructed operator. -/
theorem response_contraction (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (hscale : ∀ x : E, ‖S x‖ ^ 2 ≤ c * ‖x‖ ^ 2) (x : E) :
    ‖response L T c hc hsampling S x‖ ≤ ‖x‖ := by
  have hb := response_norm_sq_le L T c hc hsampling S x
  have hs : ‖S x‖ ^ 2 / c ≤ ‖x‖ ^ 2 := (div_le_iff₀ hc).mpr (by
    simpa [mul_comm] using hscale x)
  have hsq := hb.trans hs
  nlinarith [norm_nonneg (response L T c hc hsampling S x), norm_nonneg x]

theorem response_opNorm_le_one (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (hscale : ∀ x : E, ‖S x‖ ^ 2 ≤ c * ‖x‖ ^ 2) :
    ‖response L T c hc hsampling S‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa only [one_mul] using response_contraction L T c hc hsampling S hscale x

/-- The adjoint error response is controlled in the same Hilbert norm.
This is the deterministic contraction step in the remainder bound. -/
theorem response_adjoint_error_le (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (hscale : ∀ x : E, ‖S x‖ ^ 2 ≤ c * ‖x‖ ^ 2) (r : F) :
    ‖(response L T c hc hsampling S).adjoint r‖ ≤ ‖r‖ := by
  have hop : ‖(response L T c hc hsampling S).adjoint‖ ≤ 1 := by
    simpa using response_opNorm_le_one L T c hc hsampling S hscale
  exact ((response L T c hc hsampling S).adjoint.le_opNorm r).trans
    (mul_le_of_le_one_left (norm_nonneg _) hop)

/-- The scalar pairing form of the exact response. -/
theorem response_pairing (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (x y : E) :
    inner ℝ (response L T c hc hsampling S x) (T y) = inner ℝ (S x) y := by
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_response]

/-- Pointwise tight bound, retaining the diagonal response scale. -/
theorem response_norm_le (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    ‖response L T c hc hsampling S x‖ ≤ ‖S x‖ / Real.sqrt c := by
  have h := response_norm_sq_le L T c hc hsampling S x
  have hsqrt : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hc.le
  have hsq : (‖S x‖ / Real.sqrt c) ^ 2 = ‖S x‖ ^ 2 / c := by rw [div_pow, hsqrt]
  have hn : 0 ≤ ‖S x‖ / Real.sqrt c := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg (response L T c hc hsampling S x)]

theorem response_opNorm_le (L : Submodule ℝ F) (T : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E, c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (S : E →L[ℝ] E) :
    ‖response L T c hc hsampling S‖ ≤ ‖S‖ / Real.sqrt c := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  intro x
  calc
    _ ≤ ‖S x‖ / Real.sqrt c := response_norm_le L T c hc hsampling S x
    _ ≤ (‖S‖ * ‖x‖) / Real.sqrt c :=
      div_le_div_of_nonneg_right (S.le_opNorm x) (Real.sqrt_nonneg _)
    _ = (‖S‖ / Real.sqrt c) * ‖x‖ := by ring

section Diagonal

/-- Diagonal coordinate scaling on the genuine L² Euclidean space. -/
def diagonalLinear (r : ℕ) (s : Fin r → ℝ) :
    EuclideanSpace ℝ (Fin r) →ₗ[ℝ] EuclideanSpace ℝ (Fin r) where
  toFun x := WithLp.toLp 2 (fun j => s j * x j)
  map_add' x y := by ext j; simp [mul_add]
  map_smul' a x := by ext j; simp [smul_eq_mul]; ring

def diagonalScale (r : ℕ) (s : Fin r → ℝ) :
    EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) :=
  (diagonalLinear r s).toContinuousLinearMap

@[simp] theorem diagonalScale_apply (r : ℕ) (s : Fin r → ℝ)
    (x : EuclideanSpace ℝ (Fin r)) (j : Fin r) : diagonalScale r s x j = s j * x j := rfl

theorem diagonalScale_norm_sq_le (r : ℕ) (s : Fin r → ℝ) (c : ℝ)
    (hs : ∀ j, s j ^ 2 ≤ c) (x : EuclideanSpace ℝ (Fin r)) :
    ‖diagonalScale r s x‖ ^ 2 ≤ c * ‖x‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, diagonalScale_apply, Real.norm_eq_abs,
    sq_abs, mul_pow, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hs j) (sq_nonneg _)

/-- Coordinatewise exact shell response for an actual diagonal S. -/
theorem adjoint_response_diagonal (r : ℕ) (L : Submodule ℝ F)
    (T : EuclideanSpace ℝ (Fin r) →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : EuclideanSpace ℝ (Fin r),
      c * ‖x‖ ^ 2 ≤ ‖highProjection L (T x)‖ ^ 2)
    (s : Fin r → ℝ) (x : EuclideanSpace ℝ (Fin r)) (j : Fin r) :
    T.adjoint (response L T c hc hsampling (diagonalScale r s) x) j = s j * x j := by
  rw [adjoint_response, diagonalScale_apply]

theorem diagonalScale_adjoint_apply (r : ℕ) (s : Fin r → ℝ)
    (x : EuclideanSpace ℝ (Fin r)) (j : Fin r) :
    (diagonalScale r s).adjoint x j = s j * x j := by
  have hsingle : diagonalScale r s (EuclideanSpace.single j 1) = EuclideanSpace.single j (s j) := by
    ext i
    by_cases hi : i = j <;> simp [EuclideanSpace.single_apply, hi, diagonalScale_apply]
  calc
    _ = inner ℝ (EuclideanSpace.single j 1) ((diagonalScale r s).adjoint x) := by rw [EuclideanSpace.inner_single_left]; simp
    _ = inner ℝ (diagonalScale r s (EuclideanSpace.single j 1)) x :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = s j * x j := by rw [hsingle, EuclideanSpace.inner_single_left]; simp

theorem diagonalScale_self_adjoint (r : ℕ) (s : Fin r → ℝ) :
    (diagonalScale r s).adjoint = diagonalScale r s := by
  ext x j
  exact diagonalScale_adjoint_apply r s x j

end Diagonal

section Weighted

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The actual low sample range after applying the sampling weight. -/
def weightedLow (W : F →L[ℝ] F) (Λ : H →L[ℝ] F) : Submodule ℝ F :=
  LinearMap.range (W.comp Λ).toLinearMap

/-- Physical response with the outer adjoint weight retained:
`B = W† Π (W T₀) G⁻¹ S`. For self-adjoint diagonal weights, `W† = W`. -/
def weightedResponse (W : F →L[ℝ] F) (Λ : H →L[ℝ] F) (T₀ : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) : E →L[ℝ] F :=
  W.adjoint.comp (response (weightedLow W Λ) (W.comp T₀) c hc hsampling S)

/-- The physical response is exact for the unweighted shell samples. -/
theorem weightedResponse_exact (W : F →L[ℝ] F) (Λ : H →L[ℝ] F) (T₀ : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    T₀.adjoint (weightedResponse W Λ T₀ c hc hsampling S x) = S x := by
  have h := adjoint_response (weightedLow W Λ) (W.comp T₀) c hc hsampling S x
  simpa only [weightedResponse, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_comp] using h

/-- The physical response annihilates all unweighted low sample data. -/
theorem weightedResponse_low_zero [CompleteSpace H] (W : F →L[ℝ] F) (Λ : H →L[ℝ] F) (T₀ : E →L[ℝ] F)
    (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    Λ.adjoint (weightedResponse W Λ T₀ c hc hsampling S x) = 0 := by
  apply ext_inner_left ℝ
  intro h
  change inner ℝ h (Λ.adjoint (W.adjoint
    (response (weightedLow W Λ) (W.comp T₀) c hc hsampling S x))) = inner ℝ h 0
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    inner_zero_right]
  apply response_annihilates_low
  exact LinearMap.mem_range_self (W.comp Λ).toLinearMap h

theorem weightedResponse_adjoint_apply (W : F →L[ℝ] F) (Λ : H →L[ℝ] F)
    (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (r : F) :
    (weightedResponse W Λ T₀ c hc hsampling S).adjoint r =
      (response (weightedLow W Λ) (W.comp T₀) c hc hsampling S).adjoint (W r) := by
  simp only [weightedResponse, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_apply]

/-- Structured error transfer: the weighted remainder `W r` is retained.
No unnecessary smallness condition `‖S‖² ≤ c` is imposed. -/
theorem weightedResponse_error_le (W : F →L[ℝ] F) (Λ : H →L[ℝ] F)
    (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (r : F) :
    ‖(weightedResponse W Λ T₀ c hc hsampling S).adjoint r‖ ≤
      (‖S‖ / Real.sqrt c) * ‖W r‖ := by
  rw [weightedResponse_adjoint_apply]
  have hop : ‖(response (weightedLow W Λ) (W.comp T₀) c hc hsampling S).adjoint‖ ≤
      ‖S‖ / Real.sqrt c := by
    simpa using response_opNorm_le (weightedLow W Λ) (W.comp T₀) c hc hsampling S
  exact ((response (weightedLow W Λ) (W.comp T₀) c hc hsampling S).adjoint.le_opNorm (W r)).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg _))

theorem weightedResponse_error_sq_le (W : F →L[ℝ] F) (Λ : H →L[ℝ] F)
    (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (r : F) :
    ‖(weightedResponse W Λ T₀ c hc hsampling S).adjoint r‖ ^ 2 ≤
      (‖S‖ ^ 2 / c) * ‖W r‖ ^ 2 := by
  have h := weightedResponse_error_le W Λ T₀ c hc hsampling S r
  have hnonneg : 0 ≤ (‖S‖ / Real.sqrt c) * ‖W r‖ := by positivity
  have hsq := (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr h
  simpa only [mul_pow, div_pow, Real.sq_sqrt hc.le] using hsq

/-- The physical operator norm retains the crucial outer weight factor. -/
theorem weightedResponse_opNorm_le (W : F →L[ℝ] F) (Λ : H →L[ℝ] F)
    (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) :
    ‖weightedResponse W Λ T₀ c hc hsampling S‖ ≤ ‖W‖ * (‖S‖ / Real.sqrt c) := by
  apply (W.adjoint.opNorm_comp_le _).trans
  have h := mul_le_mul_of_nonneg_left
    (response_opNorm_le (weightedLow W Λ) (W.comp T₀) c hc hsampling S) (norm_nonneg W)
  simpa using h

theorem weightedResponse_contraction (W : F →L[ℝ] F) (Λ : H →L[ℝ] F)
    (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (hscale : ‖W‖ * (‖S‖ / Real.sqrt c) ≤ 1) (x : E) :
    ‖weightedResponse W Λ T₀ c hc hsampling S x‖ ≤ ‖x‖ :=
  ((weightedResponse W Λ T₀ c hc hsampling S).le_opNorm x).trans
    (mul_le_of_le_one_left (norm_nonneg _) ((weightedResponse_opNorm_le W Λ T₀ c hc hsampling S).trans hscale))

theorem weightedResponse_adjoint_shell (W : F →L[ℝ] F) (Λ : H →L[ℝ] F)
    (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (u : E) :
    (weightedResponse W Λ T₀ c hc hsampling S).adjoint (T₀ u) = S.adjoint u := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.adjoint_inner_left, weightedResponse_exact]

theorem weightedResponse_adjoint_low [CompleteSpace H] (W : F →L[ℝ] F)
    (Λ : H →L[ℝ] F) (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (u : H) :
    (weightedResponse W Λ T₀ c hc hsampling S).adjoint (Λ u) = 0 := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.adjoint_inner_left,
    weightedResponse_low_zero, inner_zero_left, inner_zero_right]

/-- Exact shell/low/remainder response decomposition with actual
operators and vectors. For diagonal S, S†=S is proved above. -/
theorem weightedResponse_decomposition [CompleteSpace H] (W : F →L[ℝ] F)
    (Λ : H →L[ℝ] F) (T₀ : E →L[ℝ] F) (c : ℝ) (hc : 0 < c)
    (hsampling : ∀ x : E,
      c * ‖x‖ ^ 2 ≤ ‖highProjection (weightedLow W Λ) ((W.comp T₀) x)‖ ^ 2)
    (S : E →L[ℝ] E) (u : E) (l : H) (r : F) :
    (weightedResponse W Λ T₀ c hc hsampling S).adjoint (T₀ u + Λ l + r) =
      S.adjoint u + (weightedResponse W Λ T₀ c hc hsampling S).adjoint r := by
  rw [map_add, map_add, weightedResponse_adjoint_shell, weightedResponse_adjoint_low, add_zero]

end Weighted

section SamplingCoercivity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ E] in
/-- Coercivity after removing the sampled low space follows from genuine
lower sampling on the primitive space, orthogonality to the low primitive
space and a lower norm bound for the shell synthesis. No projected-Gram
estimate is assumed here. -/
theorem projected_sampling_lower (K : Submodule ℝ V) (Q : V →L[ℝ] F)
    (U : E →L[ℝ] V) (a b : ℝ) (hb : 0 ≤ b)
    (hshell : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (horthogonal : ∀ x : E, U x ∈ Kᗮ)
    (hsample : ∀ v : V, b * ‖v‖ ^ 2 ≤ ‖Q v‖ ^ 2) (x : E) :
    (a * b) * ‖x‖ ^ 2 ≤
      ‖highProjection (K.map Q.toLinearMap) ((Q.comp U) x)‖ ^ 2 := by
  let L : Submodule ℝ F := K.map Q.toLinearMap
  have hmem : L.starProjection (Q (U x)) ∈ K.map Q.toLinearMap :=
    L.starProjection_apply_mem _
  obtain ⟨k, hk, hQk⟩ := hmem
  change Q k = L.starProjection (Q (U x)) at hQk
  have heq : highProjection L (Q (U x)) = Q (U x - k) := by
    change Lᗮ.starProjection (Q (U x)) = _
    rw [Submodule.starProjection_orthogonal_val, map_sub, hQk]
  have hinner : inner ℝ (U x) k = 0 := by
    rw [real_inner_comm]
    exact horthogonal x k hk
  have hpy : ‖U x - k‖ ^ 2 = ‖U x‖ ^ 2 + ‖k‖ ^ 2 := by
    simpa only [pow_two] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hinner
  change (a * b) * ‖x‖ ^ 2 ≤ ‖highProjection L (Q (U x))‖ ^ 2
  rw [heq]
  calc
    (a * b) * ‖x‖ ^ 2 = b * (a * ‖x‖ ^ 2) := by ring
    _ ≤ b * ‖U x‖ ^ 2 := mul_le_mul_of_nonneg_left (hshell x) hb
    _ ≤ b * ‖U x - k‖ ^ 2 := mul_le_mul_of_nonneg_left (by
      rw [hpy]
      exact le_add_of_nonneg_right (sq_nonneg _)) hb
    _ ≤ ‖Q (U x - k)‖ ^ 2 := hsample _

omit [FiniteDimensional ℝ E] in
/-- The coercivity input in the exact weighted operator language follows
from actual sampling on primitives, including the outer sampling weight. -/
theorem weighted_sampling_lower (K : Submodule ℝ V) (P : V →L[ℝ] F)
    (W : F →L[ℝ] F) (U : E →L[ℝ] V) (a b : ℝ) (hb : 0 ≤ b)
    (hshell : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (horthogonal : ∀ x : E, U x ∈ Kᗮ)
    (hsample : ∀ v : V, b * ‖v‖ ^ 2 ≤ ‖W (P v)‖ ^ 2) (x : E) :
    (a * b) * ‖x‖ ^ 2 ≤
      ‖highProjection (weightedLow W (P.comp K.subtypeL)) ((W.comp (P.comp U)) x)‖ ^ 2 := by
  have hL : weightedLow W (P.comp K.subtypeL) = K.map (W.comp P).toLinearMap := by
    ext z
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, k.property, hk⟩
    · rintro ⟨k, hk, heq⟩
      exact ⟨⟨k, hk⟩, heq⟩
  rw [hL]
  exact projected_sampling_lower K (W.comp P) U a b hb hshell horthogonal hsample x

/-- Construction whose only analytic inputs are actual norm sampling,
actual shell synthesis norms and actual low/shell orthogonality. -/
def sampledWeightedResponse (K : Submodule ℝ V) (P : V →L[ℝ] F)
    (W : F →L[ℝ] F) (U : E →L[ℝ] V) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hshell : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (horthogonal : ∀ x : E, U x ∈ Kᗮ)
    (hsample : ∀ v : V, b * ‖v‖ ^ 2 ≤ ‖W (P v)‖ ^ 2)
    (S : E →L[ℝ] E) : E →L[ℝ] F :=
  weightedResponse W (P.comp K.subtypeL) (P.comp U) (a * b) (mul_pos ha hb)
    (weighted_sampling_lower K P W U a b hb.le hshell horthogonal hsample) S

/-- Unweighted exact response derived from primitive sampling data. -/
theorem sampledWeightedResponse_exact (K : Submodule ℝ V) (P : V →L[ℝ] F)
    (W : F →L[ℝ] F) (U : E →L[ℝ] V) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hshell : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (horthogonal : ∀ x : E, U x ∈ Kᗮ)
    (hsample : ∀ v : V, b * ‖v‖ ^ 2 ≤ ‖W (P v)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    (P.comp U).adjoint (sampledWeightedResponse K P W U a b ha hb hshell horthogonal hsample S x) = S x :=
  weightedResponse_exact W (P.comp K.subtypeL) (P.comp U) (a * b) (mul_pos ha hb)
    (weighted_sampling_lower K P W U a b hb.le hshell horthogonal hsample) S x

/-- Structured remainder bound from primitive sampling data, retaining
`W r` and the actual shell/sampling lower constants. -/
theorem sampledWeightedResponse_error_le (K : Submodule ℝ V) (P : V →L[ℝ] F)
    (W : F →L[ℝ] F) (U : E →L[ℝ] V) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hshell : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (horthogonal : ∀ x : E, U x ∈ Kᗮ)
    (hsample : ∀ v : V, b * ‖v‖ ^ 2 ≤ ‖W (P v)‖ ^ 2)
    (S : E →L[ℝ] E) (r : F) :
    ‖(sampledWeightedResponse K P W U a b ha hb hshell horthogonal hsample S).adjoint r‖ ≤
      (‖S‖ / Real.sqrt (a * b)) * ‖W r‖ :=
  weightedResponse_error_le W (P.comp K.subtypeL) (P.comp U) (a * b) (mul_pos ha hb)
    (weighted_sampling_lower K P W U a b hb.le hshell horthogonal hsample) S r

theorem sampledWeightedResponse_opNorm_le (K : Submodule ℝ V) (P : V →L[ℝ] F)
    (W : F →L[ℝ] F) (U : E →L[ℝ] V) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hshell : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (horthogonal : ∀ x : E, U x ∈ Kᗮ)
    (hsample : ∀ v : V, b * ‖v‖ ^ 2 ≤ ‖W (P v)‖ ^ 2)
    (S : E →L[ℝ] E) :
    ‖sampledWeightedResponse K P W U a b ha hb hshell horthogonal hsample S‖ ≤
      ‖W‖ * (‖S‖ / Real.sqrt (a * b)) :=
  weightedResponse_opNorm_le W (P.comp K.subtypeL) (P.comp U) (a * b) (mul_pos ha hb)
    (weighted_sampling_lower K P W U a b hb.le hshell horthogonal hsample) S

theorem sampledWeightedResponse_low_zero (K : Submodule ℝ V) [CompleteSpace K]
    (P : V →L[ℝ] F) (W : F →L[ℝ] F) (U : E →L[ℝ] V)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hshell : ∀ x : E, a * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (horthogonal : ∀ x : E, U x ∈ Kᗮ)
    (hsample : ∀ v : V, b * ‖v‖ ^ 2 ≤ ‖W (P v)‖ ^ 2)
    (S : E →L[ℝ] E) (x : E) :
    (P.comp K.subtypeL).adjoint
      (sampledWeightedResponse K P W U a b ha hb hshell horthogonal hsample S x) = 0 :=
  weightedResponse_low_zero W (P.comp K.subtypeL) (P.comp U) (a * b) (mul_pos ha hb)
    (weighted_sampling_lower K P W U a b hb.le hshell horthogonal hsample) S x

end SamplingCoercivity


end Tusnady.GramResponse
