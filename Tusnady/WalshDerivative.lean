import Tusnady.Walsh

/-! Actual discrete derivatives and their Walsh energy identities. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative is the actual centered finite difference, with step two. -/
def derivative (F : Cube ι → ℝ) (i : ι) (x : Cube ι) : ℝ :=
  (F (Function.update x i true) - F (Function.update x i false)) / 2

theorem character_update_of_mem {S : Finset ι} {i : ι} (hi : i ∈ S)
    (x : Cube ι) (b : Bool) :
    character S (Function.update x i b) = bitSign b * character (S.erase i) x := by
  have hf : (fun j => bitSign (Function.update x i b j)) =
      Function.update (fun j => bitSign (x j)) i (bitSign b) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp only [Function.update_of_ne hj]
  unfold character
  rw [hf, Finset.prod_update_of_mem hi]
  simp only [Finset.sdiff_singleton_eq_erase]

theorem character_update_of_not_mem {S : Finset ι} {i : ι} (hi : i ∉ S)
    (x : Cube ι) (b : Bool) :
    character S (Function.update x i b) = character S x := by
  unfold character
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := fun h => hi (h ▸ hj)
  simp [hji]

theorem derivative_character (S : Finset ι) (i : ι) (x : Cube ι) :
    derivative (character S) i x = if i ∈ S then character (S.erase i) x else 0 := by
  unfold derivative
  by_cases hi : i ∈ S
  · rw [character_update_of_mem hi, character_update_of_mem hi, if_pos hi]
    norm_num [bitSign]
  · rw [character_update_of_not_mem hi, character_update_of_not_mem hi, if_neg hi]
    ring

theorem derivative_const_mul (a : ℝ) (F : Cube ι → ℝ) (i : ι) (x : Cube ι) :
    derivative (fun x => a * F x) i x = a * derivative F i x := by
  unfold derivative
  ring

theorem derivative_sum {κ : Type*} (s : Finset κ) (F : κ → Cube ι → ℝ)
    (i : ι) (x : Cube ι) :
    derivative (fun x => ∑ k ∈ s, F k x) i x = ∑ k ∈ s, derivative (F k) i x := by
  simp only [derivative, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- Differentiating the actual Fourier expansion requires no smoothness. -/
theorem derivative_expansion (F : Cube ι → ℝ) (i : ι) (x : Cube ι) :
    derivative F i x =
      ∑ S : Finset ι, coefficient F S *
        (if i ∈ S then character (S.erase i) x else 0) := by
  have hinv : F = synthesis (coefficient F) := by
    funext y
    exact (inversion F y).symm
  calc
    derivative F i x = derivative (synthesis (coefficient F)) i x := congrArg (fun G => derivative G i x) hinv
    _ = ∑ S : Finset ι, coefficient F S * derivative (character S) i x := by
      change derivative (fun y : Cube ι => ∑ S : Finset ι, coefficient F S * character S y) i x = _
      rw [derivative_sum]
      apply Finset.sum_congr rfl
      intro S _
      exact derivative_const_mul _ _ _ _
    _ = _ := by simp_rw [derivative_character]

/-- The energy of a finite expansion in an actually orthonormal family.
This elementary sum identity is used below with erased Walsh characters. -/
theorem mean_sq_sum_orthonormal {κ : Type*} [DecidableEq κ]
    (s : Finset κ) (a : κ → ℝ) (v : κ → Cube ι → ℝ)
    (hv : ∀ j ∈ s, ∀ k ∈ s,
      mean (fun x => v j x * v k x) = if j = k then 1 else 0) :
    mean (fun x => (∑ j ∈ s, a j * v j x) ^ 2) = ∑ j ∈ s, a j ^ 2 := by
  have heq (x : Cube ι) : (∑ j ∈ s, a j * v j x) ^ 2 =
      ∑ j ∈ s, ∑ k ∈ s, (a j * a k) * (v j x * v k x) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [heq, mean_sum, mean_const_mul]
  apply Finset.sum_congr rfl
  intro j hj
  apply Eq.trans (Finset.sum_congr rfl (fun k hk => by rw [hv j hj k hk]))
  simp [hj, pow_two]

/-- Parseval for an actual first discrete derivative. -/
theorem derivative_parseval (F : Cube ι → ℝ) (i : ι) :
    mean (fun x => derivative F i x ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => i ∈ S), coefficient F S ^ 2 := by
  let s : Finset (Finset ι) := Finset.univ.filter (fun S => i ∈ S)
  have heq (x : Cube ι) : derivative F i x =
      ∑ S ∈ s, coefficient F S * character (S.erase i) x := by
    rw [derivative_expansion]
    simp [s, Finset.sum_filter, mul_ite]
  simp_rw [heq]
  apply mean_sq_sum_orthonormal s (coefficient F) (fun S x => character (S.erase i) x)
  intro S hS T hT
  have hiS : i ∈ S := (Finset.mem_filter.mp hS).2
  have hiT : i ∈ T := (Finset.mem_filter.mp hT).2
  rw [character_orthogonality]
  have hi : S.erase i = T.erase i ↔ S = T := by
    constructor
    · intro h
      calc
        S = insert i (S.erase i) := (Finset.insert_erase hiS).symm
        _ = insert i (T.erase i) := congrArg (insert i) h
        _ = T := Finset.insert_erase hiT
    · rintro rfl
      rfl
  simp only [hi]

/-- The mean finite derivative is exactly the first Fourier coefficient. -/
theorem mean_derivative (F : Cube ι → ℝ) (i : ι) :
    mean (fun x => derivative F i x) = coefficient F {i} := by
  have heq : (fun x => derivative F i x) = fun x =>
      ∑ S : Finset ι, coefficient F S *
        (if i ∈ S then character (S.erase i) x else 0) := by
    funext x
    exact derivative_expansion F i x
  rw [heq, mean_sum]
  have hsum : (∑ S : Finset ι, mean (fun x => coefficient F S *
      (if i ∈ S then character (S.erase i) x else 0))) =
      ∑ S : Finset ι, if S = {i} then coefficient F S else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    by_cases hs : S = {i}
    · subst S
      simp
    · rw [if_neg hs]
      by_cases hi : i ∈ S
      · have hne : S.erase i ≠ ∅ := by
          intro he
          apply hs
          calc
            S = insert i (S.erase i) := (Finset.insert_erase hi).symm
            _ = {i} := by rw [he]; rfl
        have hz : mean (fun x : Cube ι => character (S.erase i) x) = 0 := by
          simpa [hne] using character_orthogonality (S.erase i) ∅
        simpa only [if_pos hi, mean_const_mul, hz, mul_zero]
      · simp only [if_neg hi, mul_zero, mean_const]
  rw [hsum]
  simp

end Tusnady.Walsh
