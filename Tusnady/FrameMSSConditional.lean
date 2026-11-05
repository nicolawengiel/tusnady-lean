import Tusnady.External.RealRooted.MultivariateStability.ExpectedCharpoly
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-! # Actual finite independent vector distributions for MSS

Second moments are genuine finite sums of rank-one matrices. Conditioning
fixes an actual coordinate to a point mass. Weighted recombination of these
conditional characteristic polynomials is proved from the finite product law.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Tusnady.FrameMSS
attribute [local instance] Classical.propDecidable
open RealRooted.MixedCharacteristic

variable {m n : ℕ} {κ : Type} [Fintype κ]

def expected (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ) : ℝ[X] :=
  expectedCharpoly (fun _ => κ) v p

theorem secondMoment_posSemidef (v : κ → Fin n → ℝ) (p : κ → ℝ)
    (hp : ∀ a, 0 ≤ p a) : (secondMoment v p).PosSemidef := by
  classical
  have hsum (S : Finset κ) : (∑ a ∈ S, p a • Matrix.vecMulVec (v a) (v a)).PosSemidef := by
    induction S using Finset.induction_on with
    | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
    | insert a S ha hS =>
      rw [Finset.sum_insert ha]
      have hrank : (Matrix.vecMulVec (v a) (v a)).PosSemidef := by
        simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (v a)
      exact (hrank.smul (hp a)).add hS
  exact hsum Finset.univ

theorem secondMoment_trace (v : κ → Fin n → ℝ) (p : κ → ℝ) :
    (secondMoment v p).trace = ∑ a, p a * ∑ j, (v a j) ^ 2 := by
  rw [secondMoment, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.trace_smul]
  simp only [smul_eq_mul, Matrix.trace, Matrix.diag_apply, Matrix.vecMulVec_apply, pow_two]

theorem expected_monic (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) : (expected v p).Monic := by
  rw [expected, expectedCharpoly_eq_mixedCharacteristic _ _ _ hp]
  exact mixedCharacteristic_monic _

theorem expected_natDegree (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) : (expected v p).natDegree = n := by
  rw [expected, expectedCharpoly_eq_mixedCharacteristic _ _ _ hp]
  exact natDegree_mixedCharacteristic _

theorem expected_splits (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ)
    (hpn : ∀ i a, 0 ≤ p i a) (hp : ∀ i, ∑ a, p i a = 1) :
    (expected v p).Splits (RingHom.id ℝ) := by
  rw [expected, expectedCharpoly_eq_mixedCharacteristic _ _ _ hp]
  exact mixedCharacteristic_splits _ (fun i => secondMoment_posSemidef _ _ (hpn i))

def pointProbability (a b : κ) : ℝ := if b = a then 1 else 0

omit [Fintype κ] in
theorem pointProbability_nonneg (a b : κ) : 0 ≤ pointProbability a b := by
  classical
  unfold pointProbability
  split <;> norm_num

theorem pointProbability_sum (a : κ) : ∑ b, pointProbability a b = 1 := by
  classical
  simp [pointProbability]

def freeze (p : Fin m → κ → ℝ) (j : Fin m) (a : κ) : Fin m → κ → ℝ :=
  Function.update p j (pointProbability a)

omit [Fintype κ] in
theorem freeze_nonneg (p : Fin m → κ → ℝ) (hpn : ∀ i a, 0 ≤ p i a)
    (j : Fin m) (a : κ) : ∀ i b, 0 ≤ freeze p j a i b := by
  classical
  intro i b
  by_cases hi : i = j
  · subst i; simp only [freeze, Function.update_self]; exact pointProbability_nonneg _ _
  · rw [freeze, Function.update_of_ne hi]; exact hpn i b

theorem freeze_normalized (p : Fin m → κ → ℝ) (hp : ∀ i, ∑ a, p i a = 1)
    (j : Fin m) (a : κ) : ∀ i, ∑ b, freeze p j a i b = 1 := by
  classical
  intro i
  by_cases hi : i = j
  · subst i; simp only [freeze, Function.update_self]; exact pointProbability_sum _
  · rw [freeze, Function.update_of_ne hi]; exact hp i

/-- Recombination is exactly the actual independent law with one changed marginal. -/
theorem expected_recombine (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ)
    (j : Fin m) (w : κ → ℝ) :
    (∑ a, w a • expected v (freeze p j a)) = expected v (Function.update p j w) := by
  classical
  unfold expected expectedCharpoly
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [← Finset.sum_smul]
  congr 1
  have hprod (a : κ) :
      (∏ i, freeze p j a i (s i)) =
        pointProbability a (s j) * ∏ i ∈ {j}ᶜ, p i (s i) := by
    rw [Fintype.prod_eq_mul_prod_compl j]
    simp only [freeze, Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    exact congrFun (Function.update_of_ne (by simpa using hi) (pointProbability a) p) (s i)
  simp_rw [hprod, ← mul_assoc]
  rw [← Finset.sum_mul]
  have hw : (∑ a, w a * pointProbability a (s j)) = w (s j) := by
    simp [pointProbability, eq_comm]
  rw [hw, Fintype.prod_eq_mul_prod_compl j]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi =>
    (congrFun (Function.update_of_ne (by simpa using hi) w p) (s i)).symm

/-- Every convex combination needed by one MSS choice is genuinely split. -/
theorem conditional_combinations_split (v : Fin m → κ → Fin n → ℝ)
    (p : Fin m → κ → ℝ) (hpn : ∀ i a, 0 ≤ p i a) (hp : ∀ i, ∑ a, p i a = 1)
    (j : Fin m) (w : κ → ℝ) (hwn : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1) :
    (∑ a, w a • expected v (freeze p j a)).Splits (RingHom.id ℝ) := by
  classical
  rw [expected_recombine]
  apply expected_splits
  · intro i a
    by_cases hi : i = j
    · subst i; simp only [Function.update_self]; exact hwn a
    · rw [Function.update_of_ne hi]; exact hpn i a
  · intro i
    by_cases hi : i = j
    · subst i; simp only [Function.update_self]; exact hw
    · rw [Function.update_of_ne hi]; exact hp i

/-- Recombining at the current marginal gives the current expected polynomial. -/
theorem expected_recombine_current (v : Fin m → κ → Fin n → ℝ)
    (p : Fin m → κ → ℝ) (j : Fin m) :
    (∑ a, p j a • expected v (freeze p j a)) = expected v p := by
  rw [expected_recombine, Function.update_eq_self]

/-- Once every coordinate is fixed, the expectation is the actual realized matrix polynomial. -/
theorem expected_pointProbabilities (v : Fin m → κ → Fin n → ℝ) (s : Fin m → κ) :
    expected v (fun i => pointProbability (s i)) =
      (∑ i, Matrix.vecMulVec (v i (s i)) (v i (s i))).charpoly := by
  classical
  unfold expected expectedCharpoly
  rw [Finset.sum_eq_single s]
  · simp [pointProbability]
  · intro t _ hts
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hts
    have hz : (∏ j, pointProbability (s j) (t j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [pointProbability, hi]
    rw [hz, zero_smul]
  · simp

/-- The first `k` coordinates have been observed; the others retain their original law. -/
def prefixCondition (p : Fin m → κ → ℝ) (k : ℕ) (s : Fin m → κ) : Fin m → κ → ℝ :=
  fun i => if i.val < k then pointProbability (s i) else p i

omit [Fintype κ] in
theorem prefixCondition_nonneg (p : Fin m → κ → ℝ) (hpn : ∀ i a, 0 ≤ p i a)
    (k : ℕ) (s : Fin m → κ) : ∀ i a, 0 ≤ prefixCondition p k s i a := by
  intro i a
  unfold prefixCondition
  split
  · exact pointProbability_nonneg _ _
  · exact hpn i a

theorem prefixCondition_normalized (p : Fin m → κ → ℝ) (hp : ∀ i, ∑ a, p i a = 1)
    (k : ℕ) (s : Fin m → κ) : ∀ i, ∑ a, prefixCondition p k s i a = 1 := by
  intro i
  unfold prefixCondition
  split
  · exact pointProbability_sum _
  · exact hp i

omit [Fintype κ] in
theorem prefixCondition_zero (p : Fin m → κ → ℝ) (s : Fin m → κ) :
    prefixCondition p 0 s = p := by
  funext i
  simp [prefixCondition]

omit [Fintype κ] in
theorem prefixCondition_full (p : Fin m → κ → ℝ) (s : Fin m → κ) :
    prefixCondition p m s = fun i => pointProbability (s i) := by
  funext i
  simp only [prefixCondition, i.isLt, ↓reduceIte]

omit [Fintype κ] in
theorem prefixCondition_next (p : Fin m → κ → ℝ) {k : ℕ} (hk : k < m)
    (s : Fin m → κ) (a : κ) :
    prefixCondition p (k+1) (Function.update s ⟨k,hk⟩ a) =
      freeze (prefixCondition p k s) ⟨k,hk⟩ a := by
  classical
  funext i b
  by_cases hi : i = (⟨k,hk⟩ : Fin m)
  · subst i
    simp [prefixCondition, freeze]
  · have hival : i.val ≠ k := fun h => hi (Fin.ext h)
    have heq : i.val < k+1 ↔ i.val < k := by omega
    simp only [prefixCondition, heq, Function.update_of_ne hi, freeze]

omit [Fintype κ] in
theorem prefixCondition_current (p : Fin m → κ → ℝ) {k : ℕ} (hk : k < m)
    (s : Fin m → κ) : prefixCondition p k s ⟨k,hk⟩ = p ⟨k,hk⟩ := by
  simp [prefixCondition]

end Tusnady.FrameMSS
