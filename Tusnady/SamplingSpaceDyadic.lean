import Tusnady.SamplingSpaceBase
import Tusnady.HaarFunctions

/-!
# Actual dyadic affine basis and its pointwise Christoffel function

The basis is localized on the project's real half-open dyadic intervals.
All evaluations use these explicit representatives, including endpoints.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Tusnady.SamplingSpace
open DyadicFunctions

abbrev BasisIndex (j : ℕ) := Fin (2 ^ j) × Bool

/-- Local coordinate of a point in the actual dyadic interval. -/
def localCoordinate (j : ℕ) (i : Fin (2 ^ j)) (x : ℝ) : ℝ :=
  (x - dyadicLeft j i) / dyadicLength j

/-- The concrete normalized constant/linear mode in one dyadic cell. -/
def basis (j : ℕ) (ib : BasisIndex j) (x : ℝ) : ℝ :=
  Real.sqrt ((2 : ℝ) ^ j) * baseBasis ib.2 (localCoordinate j ib.1 x)

lemma localCoordinate_mem_iff (j : ℕ) (i : Fin (2 ^ j)) (x : ℝ) :
    localCoordinate j i x ∈ Ico (0 : ℝ) 1 ↔ x ∈ dyadicInterval j i :=
  normalized_mem_unit_iff _ _ _ (dyadicLength_pos j)

/-- Explicit representative as a polynomial times the cell indicator. -/
theorem basis_eq_indicator (j : ℕ) (ib : BasisIndex j) :
    basis j ib = (dyadicInterval j ib.1).indicator
      (fun x => Real.sqrt ((2 : ℝ) ^ j) * affineMode ib.2 (localCoordinate j ib.1 x)) := by
  funext x
  by_cases hx : x ∈ dyadicInterval j ib.1
  · have hn := (localCoordinate_mem_iff j ib.1 x).mpr hx
    simp [basis, baseBasis, unitPatch, hx, hn]
  · have hn : localCoordinate j ib.1 x ∉ Ico (0 : ℝ) 1 :=
      fun h => hx ((localCoordinate_mem_iff j ib.1 x).mp h)
    simp [basis, baseBasis, unitPatch, hx, hn]

lemma basis_zero_outside (j : ℕ) (ib : BasisIndex j) (x : ℝ)
    (hx : x ∉ dyadicInterval j ib.1) : basis j ib x = 0 := by
  rw [basis_eq_indicator]
  simp [hx]

lemma localMode_continuous (j : ℕ) (ib : BasisIndex j) :
    Continuous (fun x => Real.sqrt ((2 : ℝ) ^ j) * affineMode ib.2 (localCoordinate j ib.1 x)) := by
  unfold localCoordinate
  exact continuous_const.mul ((affineMode_continuous ib.2).comp
    ((continuous_id.sub continuous_const).div_const _))

lemma basis_memLp (j : ℕ) (ib : BasisIndex j) : MemLp (basis j ib) 2 (volume : Measure ℝ) := by
  rw [basis_eq_indicator]
  apply (memLp_two_iff_integrable_sq ?_).mpr
  · have heq : (fun x => ((dyadicInterval j ib.1).indicator
        (fun x => Real.sqrt ((2 : ℝ) ^ j) * affineMode ib.2 (localCoordinate j ib.1 x)) x) ^ 2) =
        (dyadicInterval j ib.1).indicator
          (fun x => (Real.sqrt ((2 : ℝ) ^ j) * affineMode ib.2 (localCoordinate j ib.1 x)) ^ 2) := by
      funext x
      by_cases hx : x ∈ dyadicInterval j ib.1 <;> simp [hx]
    rw [heq]
    unfold dyadicInterval
    rw [integrable_indicator_iff measurableSet_Ico]
    exact ((localMode_continuous j ib).pow 2).integrableOn_Icc.mono_set Ico_subset_Icc_self
  · exact ((localMode_continuous j ib).measurable.indicator measurableSet_Ico).aestronglyMeasurable

/-- The same-cell product integral is obtained by an actual affine
change of variables, including the factor `2^j * 2^-j = 1`. -/
theorem basis_inner_same_cell (j : ℕ) (i : Fin (2 ^ j)) (b c : Bool) :
    (∫ x, basis j (i, b) x * basis j (i, c) x) = if b = c then 1 else 0 := by
  have hsqrt : (Real.sqrt ((2 : ℝ) ^ j)) ^ 2 = (2 : ℝ) ^ j :=
    Real.sq_sqrt (by positivity)
  have hf : (fun x => basis j (i, b) x * basis j (i, c) x) =
      (fun x => (2 : ℝ) ^ j *
        (fun t => baseBasis b t * baseBasis c t) ((x - dyadicLeft j i) / dyadicLength j)) := by
    funext x
    change (Real.sqrt ((2 : ℝ) ^ j) * baseBasis b (localCoordinate j i x)) *
      (Real.sqrt ((2 : ℝ) ^ j) * baseBasis c (localCoordinate j i x)) = _
    calc
      _ = (Real.sqrt ((2 : ℝ) ^ j)) ^ 2 *
          (baseBasis b (localCoordinate j i x) * baseBasis c (localCoordinate j i x)) := by ring
      _ = _ := by rw [hsqrt]; rfl
  rw [hf, integral_const_mul]
  rw [integral_affine_pullback (fun t => baseBasis b t * baseBasis c t)
    (dyadicLeft j i) (dyadicLength j) (dyadicLength_pos j), baseBasis_inner]
  unfold dyadicLength
  split_ifs <;> simp [pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0)]

/-- Orthonormality of all `2^(j+1)` genuine dyadic affine functions. -/
theorem basis_inner (j : ℕ) (ib kc : BasisIndex j) :
    (∫ x, basis j ib x * basis j kc x) = if ib = kc then 1 else 0 := by
  classical
  obtain ⟨i, b⟩ := ib
  obtain ⟨k, c⟩ := kc
  by_cases hik : i = k
  · subst k
    simpa using basis_inner_same_cell j i b c
  · have hz : (fun x => basis j (i, b) x * basis j (k, c) x) = fun _ => 0 := by
      funext x
      by_cases hx : x ∈ dyadicInterval j i
      · have hk : x ∉ dyadicInterval j k := fun h =>
          (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth j i k hik)) hx h
        rw [basis_zero_outside j (k, c) x hk, mul_zero]
      · rw [basis_zero_outside j (i, b) x hx, zero_mul]
    rw [hz]
    simp [hik]

/-- Exact number of the explicit pointwise basis functions. -/
theorem basisIndex_card (j : ℕ) : Fintype.card (BasisIndex j) = 2 ^ (j + 1) := by
  simp [BasisIndex, pow_succ]

def basisChristoffel (j : ℕ) (x : ℝ) : ℝ := ∑ ib : BasisIndex j, basis j ib x ^ 2

/-- Exact pointwise basis square sum on every actual half-open cell. -/
theorem basisChristoffel_on_cell (j : ℕ) (i : Fin (2 ^ j)) (x : ℝ)
    (hx : x ∈ dyadicInterval j i) :
    basisChristoffel j x = (2 : ℝ) ^ j *
      (1 + 12 * (localCoordinate j i x - 1 / 2) ^ 2) := by
  classical
  have hn := (localCoordinate_mem_iff j i x).mpr hx
  have hsqrt : (Real.sqrt ((2 : ℝ) ^ j)) ^ 2 = (2 : ℝ) ^ j :=
    Real.sq_sqrt (by positivity)
  unfold basisChristoffel
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp only [basis, mul_pow, hsqrt, ← Finset.mul_sum]
    rw [baseBasis_christoffel _ hn]
  · intro k _ hki
    have hnot : x ∉ dyadicInterval j k := fun hk =>
      (Set.disjoint_left.mp (dyadicInterval_disjoint_same_depth j k i hki)) hk hx
    apply Finset.sum_eq_zero
    intro b _
    rw [basis_zero_outside j (k, b) x hnot]
    simp
  · intro h
    exact False.elim (h (Finset.mem_univ i))

/-- Uniform genuine pointwise Christoffel bounds on `[0,1)`. -/
theorem basisChristoffel_bounds (j : ℕ) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    (2 : ℝ) ^ j ≤ basisChristoffel j x ∧ basisChristoffel j x ≤ 4 * (2 : ℝ) ^ j := by
  obtain ⟨i, hi, _⟩ := Haar.existsUnique_unit_interval j x hx
  rw [basisChristoffel_on_cell j i x hi]
  have hs := (localCoordinate_mem_iff j i x).mpr hi
  have hpoly : 1 ≤ 1 + 12 * (localCoordinate j i x - 1 / 2) ^ 2 ∧
      1 + 12 * (localCoordinate j i x - 1 / 2) ^ 2 ≤ 4 := by
    constructor
    · nlinarith [sq_nonneg (localCoordinate j i x - 1 / 2)]
    · nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2.le)]
  constructor
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left hpoly.1 (by positivity : 0 ≤ (2 : ℝ) ^ j)
  · simpa only [mul_comm (4 : ℝ)] using
      mul_le_mul_of_nonneg_left hpoly.2 (by positivity : 0 ≤ (2 : ℝ) ^ j)

end Tusnady.SamplingSpace
