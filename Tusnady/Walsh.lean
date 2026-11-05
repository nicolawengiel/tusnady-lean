import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Finite Fourier--Walsh analysis on an actual Boolean cube

The characters, Fourier coefficients and averages below are concrete finite
sums. This module develops the finite identities used by Main.pdf §2.3;
no orthogonality, inversion or Parseval property is postulated.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh

abbrev Cube (ι : Type*) := ι → Bool

def bitSign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num [bitSign]

@[simp] theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  simpa only [pow_two] using bitSign_sq b

@[simp] theorem bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by
  cases b <;> norm_num [bitSign]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def character (S : Finset ι) (x : Cube ι) : ℝ := ∏ i ∈ S, bitSign (x i)

def mean (f : Cube ι → ℝ) : ℝ := (∑ x, f x) / (Fintype.card (Cube ι) : ℝ)

def coefficient (F : Cube ι → ℝ) (S : Finset ι) : ℝ :=
  mean (fun x => F x * character S x)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem character_empty (x : Cube ι) : character ∅ x = 1 := by
  simp [character]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem character_sq (S : Finset ι) (x : Cube ι) : character S x ^ 2 = 1 := by
  simp only [character, ← Finset.prod_pow, bitSign_sq, Finset.prod_const_one]

@[simp] theorem character_mul_self (S : Finset ι) (x : Cube ι) :
    character S x * character S x = 1 := by
  simpa only [pow_two] using character_sq S x

@[simp] theorem mean_const (a : ℝ) : mean (fun _ : Cube ι => a) = a := by
  simp [mean]

theorem mean_add (f g : Cube ι → ℝ) :
    mean (fun x => f x + g x) = mean f + mean g := by
  simp only [mean, Finset.sum_add_distrib, add_div]

theorem mean_mul_const (f : Cube ι → ℝ) (a : ℝ) :
    mean (fun x => f x * a) = mean f * a := by
  simp only [mean, ← Finset.sum_mul]
  ring

theorem mean_const_mul (f : Cube ι → ℝ) (a : ℝ) :
    mean (fun x => a * f x) = a * mean f := by
  simp only [mean, ← Finset.mul_sum]
  ring

theorem mean_sum {κ : Type*} (s : Finset κ) (f : κ → Cube ι → ℝ) :
    mean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, mean (f i) := by
  simp only [mean, ← Finset.sum_div]
  rw [Finset.sum_comm]

/-- Summing a product of coordinate functions over the Boolean cube factors. -/
theorem sum_coordinate_product (f : ι → Bool → ℝ) :
    (∑ x : Cube ι, ∏ i, f i (x i)) = ∏ i, (f i true + f i false) := by
  rw [← Fintype.prod_sum]
  simp only [Fintype.sum_bool]

/-- Walsh reproducing kernel, summed over all subsets of coordinates. -/
theorem character_kernel (x y : Cube ι) :
    (∑ S : Finset ι, character S x * character S y) =
      if x = y then (Fintype.card (Cube ι) : ℝ) else 0 := by
  have hprod : (∑ S : Finset ι, character S x * character S y) =
      ∏ i : ι, (1 + bitSign (x i) * bitSign (y i)) := by
    simp only [character, ← Finset.prod_mul_distrib]
    simpa only [Finset.prod_one_add, Finset.powerset_univ] using
      (Finset.prod_one_add (f := fun i => bitSign (x i) * bitSign (y i)) Finset.univ).symm
  rw [hprod]
  split_ifs with hxy
  · subst y
    norm_num
  · have hne : ∃ i, x i ≠ y i := by
      by_contra! h
      exact hxy (funext h)
    obtain ⟨i, hi⟩ := hne
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [bitSign]

/-- Inversion is an equality of the actual finite Fourier expansion and F. -/
theorem inversion (F : Cube ι → ℝ) (x : Cube ι) :
    (∑ S : Finset ι, coefficient F S * character S x) = F x := by
  have hcard : (Fintype.card (Cube ι) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [coefficient, mean, div_mul_eq_mul_div, ← Finset.sum_div]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hsum : (∑ y : Cube ι, ∑ S : Finset ι,
      F y * character S y * character S x) =
      ∑ y : Cube ι, F y * (if y = x then (Fintype.card (Cube ι) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro y _
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, character_kernel]
  rw [hsum]
  simp

/-- Parseval in bilinear form. -/
theorem parseval_inner (F G : Cube ι → ℝ) :
    (∑ S : Finset ι, coefficient F S * coefficient G S) =
      mean (fun x => F x * G x) := by
  conv_lhs => arg 2; ext S; arg 1; unfold coefficient mean
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  calc
    (∑ S : Finset ι, F x * character S x * coefficient G S) =
        F x * (∑ S : Finset ι, coefficient G S * character S x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = F x * G x := by rw [inversion]

theorem parseval (F : Cube ι → ℝ) :
    (∑ S : Finset ι, coefficient F S ^ 2) = mean (fun x => F x ^ 2) := by
  simpa only [pow_two] using parseval_inner F F

/-- Coordinate characters are orthonormal for uniform counting probability. -/
theorem character_orthogonality (S T : Finset ι) :
    mean (fun x => character S x * character T x) = if S = T then 1 else 0 := by
  classical
  by_cases hST : S = T
  · subst T
    simp
  · rw [if_neg hST]
    have hne : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra! h
      exact hST (Finset.ext h)
    obtain ⟨i, hi⟩ := hne
    let f : ι → Bool → ℝ := fun j b =>
      (if j ∈ S then bitSign b else 1) * (if j ∈ T then bitSign b else 1)
    have hp (x : Cube ι) : character S x * character T x = ∏ j, f j (x j) := by
      dsimp only [f]
      rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Fintype.prod_ite_mem]
      rfl
    have hz : f i true + f i false = 0 := by
      by_cases hs : i ∈ S <;> by_cases ht : i ∈ T <;>
        simp_all [f, bitSign]
    unfold mean
    simp_rw [hp]
    rw [sum_coordinate_product, Finset.prod_eq_zero (Finset.mem_univ i) hz]
    simp

theorem coefficient_character (S T : Finset ι) :
    coefficient (character S) T = if S = T then 1 else 0 :=
  character_orthogonality S T

/-- Synthesis of an arbitrary finite coefficient vector. -/
def synthesis (a : Finset ι → ℝ) (x : Cube ι) : ℝ :=
  ∑ S : Finset ι, a S * character S x

theorem coefficient_synthesis (a : Finset ι → ℝ) (T : Finset ι) :
    coefficient (synthesis a) T = a T := by
  unfold coefficient synthesis
  simp_rw [Finset.sum_mul]
  rw [mean_sum]
  simp_rw [mul_assoc, mean_const_mul, character_orthogonality]
  simp

theorem parseval_synthesis (a : Finset ι → ℝ) :
    mean (fun x => synthesis a x ^ 2) = ∑ S : Finset ι, a S ^ 2 := by
  rw [← parseval]
  simp only [coefficient_synthesis]

theorem mean_mono (f g : Cube ι → ℝ) (h : ∀ x, f x ≤ g x) : mean f ≤ mean g := by
  unfold mean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => h x) (by positivity)

theorem mean_nonneg (f : Cube ι → ℝ) (h : ∀ x, 0 ≤ f x) : 0 ≤ mean f := by
  unfold mean
  exact div_nonneg (Finset.sum_nonneg fun x _ => h x) (by positivity)

theorem abs_mean_le (f : Cube ι → ℝ) : |mean f| ≤ mean (fun x => |f x|) := by
  unfold mean
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Fintype.card (Cube ι))]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)

/-- The multilinear Fourier polynomial, with unrestricted real arguments. -/
def extension (F : Cube ι → ℝ) (y : ι → ℝ) : ℝ :=
  ∑ S : Finset ι, coefficient F S * ∏ i ∈ S, y i

/-- The same polynomial is an actual average over biased sign weights. -/
theorem extension_eq_weighted_mean (F : Cube ι → ℝ) (y : ι → ℝ) :
    extension F y = mean (fun x => F x * ∏ i, (1 + bitSign (x i) * y i)) := by
  have hp (x : Cube ι) : (∏ i, (1 + bitSign (x i) * y i)) =
      ∑ S : Finset ι, character S x * ∏ i ∈ S, y i := by
    rw [Finset.prod_one_add]
    simp only [Finset.powerset_univ, character, Finset.prod_mul_distrib]
  simp_rw [hp, Finset.mul_sum]
  rw [mean_sum]
  unfold extension coefficient
  apply Finset.sum_congr rfl
  intro S _
  rw [← mean_mul_const]
  congr 1
  funext x
  ring

/-- The biased sign weights sum to one after division by the cube size. -/
theorem mean_extension_weights (y : ι → ℝ) :
    mean (fun x : Cube ι => ∏ i, (1 + bitSign (x i) * y i)) = 1 := by
  unfold mean
  dsimp only
  rw [sum_coordinate_product (fun i b => 1 + bitSign b * y i)]
  have hp (i : ι) : (1 + bitSign true * y i) + (1 + bitSign false * y i) = 2 := by
    norm_num [bitSign] <;> ring
  simp_rw [hp]
  simp

/-- The multilinear extension preserves the uniform bound on the cube.
This is the bound used to make every product factor positive in §3. -/
theorem abs_extension_le {F : Cube ι → ℝ} (hF : ∀ x, |F x| ≤ 1)
    {y : ι → ℝ} (hy : ∀ i, |y i| ≤ 1) : |extension F y| ≤ 1 := by
  rw [extension_eq_weighted_mean]
  have hw (x : Cube ι) : 0 ≤ ∏ i, (1 + bitSign (x i) * y i) := by
    apply Finset.prod_nonneg
    intro i _
    have hi := (abs_le.mp (hy i))
    cases hx : x i <;> simp [bitSign, hx] <;> linarith
  calc
    _ ≤ mean (fun x => |F x * ∏ i, (1 + bitSign (x i) * y i)|) := abs_mean_le _
    _ ≤ mean (fun x => ∏ i, (1 + bitSign (x i) * y i)) := by
      apply mean_mono
      intro x
      rw [abs_mul, abs_of_nonneg (hw x)]
      simpa using mul_le_mul_of_nonneg_right (hF x) (hw x)
    _ = 1 := mean_extension_weights y

/-- Reindexing the uniform finite cube by a bijection preserves the mean. -/
theorem mean_reindex (e : Cube ι ≃ Cube ι) (F : Cube ι → ℝ) :
    mean (fun x => F (e x)) = mean F := by
  unfold mean
  rw [e.sum_comp]

/-- Negating every sign is a genuine cube equivalence. -/
def negateCube : Cube ι ≃ Cube ι where
  toFun x i := !(x i)
  invFun x i := !(x i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem character_negate (S : Finset ι) (x : Cube ι) :
    character S (negateCube x) = (-1 : ℝ) ^ S.card * character S x := by
  simp only [character, negateCube, Equiv.coe_fn_mk, bitSign_not, Finset.prod_neg]

theorem mean_neg (F : Cube ι → ℝ) : mean (fun x => -F x) = -mean F := by
  simp only [mean, Finset.sum_neg_distrib, neg_div]

/-- Odd block functions have no even-order Fourier coefficients. -/
theorem coefficient_even_eq_zero {F : Cube ι → ℝ}
    (hodd : ∀ x, F (negateCube x) = -F x) (S : Finset ι) (hS : Even S.card) :
    coefficient F S = 0 := by
  have heq (x : Cube ι) : F (negateCube x) * character S (negateCube x) =
      -(F x * character S x) := by
    rw [hodd, character_negate, hS.neg_one_pow]
    ring
  have h := mean_reindex negateCube (fun x => F x * character S x)
  simp only [heq, mean_neg] at h
  unfold coefficient
  linarith

/-- A permutation of coordinate labels induces a cube equivalence. -/
def permuteCube (e : ι ≃ ι) : Cube ι ≃ Cube ι where
  toFun x i := x (e i)
  invFun x i := x (e.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

/-- The sum of the signs is invariant under coordinate permutations. -/
theorem sign_sum_permute (e : ι ≃ ι) (x : Cube ι) :
    (∑ i, bitSign (permuteCube e x i)) = ∑ i, bitSign (x i) := by
  change (∑ i, bitSign (x (e i))) = _
  exact e.sum_comp (fun i => bitSign (x i))

end Tusnady.Walsh
