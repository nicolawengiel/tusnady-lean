import Tusnady.WalshDerivative

/-! Higher finite differences from the actual Walsh expansion. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Walsh
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An explicit spectral formula, subsequently identified with actual
iterated finite differences by its base case and insert recurrence. -/
def subsetDerivative (K : Finset ι) (F : Cube ι → ℝ) (x : Cube ι) : ℝ :=
  ∑ S : Finset ι, if K ⊆ S then coefficient F S * character (S \ K) x else 0

theorem subsetDerivative_empty (F : Cube ι → ℝ) (x : Cube ι) :
    subsetDerivative ∅ F x = F x := by
  simpa only [subsetDerivative, Finset.empty_subset, if_true, Finset.sdiff_empty] using inversion F x

/-- Inserting a fresh coordinate is precisely the actual discrete derivative. -/
theorem subsetDerivative_insert (K : Finset ι) (F : Cube ι → ℝ)
    (i : ι) (hi : i ∉ K) (x : Cube ι) :
    derivative (subsetDerivative K F) i x = subsetDerivative (insert i K) F x := by
  unfold subsetDerivative
  rw [derivative_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hKS : K ⊆ S
  · simp only [if_pos hKS]
    rw [derivative_const_mul, derivative_character]
    by_cases hiS : i ∈ S
    · have hiSK : i ∈ S \ K := Finset.mem_sdiff.mpr ⟨hiS, hi⟩
      have hins : insert i K ⊆ S := Finset.insert_subset_iff.mpr ⟨hiS, hKS⟩
      rw [if_pos hiSK, if_pos hins]
      have hsets : (S \ K).erase i = S \ insert i K := by
        ext j
        simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
        tauto
      rw [hsets]
    · have hiSK : i ∉ S \ K := fun h => hiS (Finset.mem_sdiff.mp h).1
      have hins : ¬ insert i K ⊆ S := fun h => hiS (h (Finset.mem_insert_self _ _))
      rw [if_neg hiSK, if_neg hins, mul_zero]
  · have hins : ¬ insert i K ⊆ S := fun h => hKS ((Finset.subset_insert _ _).trans h)
    simp only [if_neg hKS, if_neg hins, derivative]
    ring

/-- Erasing the same K is injective among sets containing K. -/
theorem sdiff_injective_on_supersets (K S T : Finset ι)
    (hKS : K ⊆ S) (hKT : K ⊆ T) : S \ K = T \ K ↔ S = T := by
  constructor
  · intro h
    ext j
    by_cases hj : j ∈ K
    · simp only [hKS hj, hKT hj]
    · simpa only [Finset.mem_sdiff, hj, not_false_eq_true, and_true] using
        (Finset.ext_iff.mp h j)
  · rintro rfl
    rfl

/-- Exact Parseval energy for any set of differentiated coordinates. -/
theorem subsetDerivative_parseval (K : Finset ι) (F : Cube ι → ℝ) :
    mean (fun x => subsetDerivative K F x ^ 2) =
      ∑ S ∈ (Finset.univ : Finset (Finset ι)).filter (fun S => K ⊆ S), coefficient F S ^ 2 := by
  let s : Finset (Finset ι) := Finset.univ.filter (fun S => K ⊆ S)
  have heq (x : Cube ι) : subsetDerivative K F x =
      ∑ S ∈ s, coefficient F S * character (S \ K) x := by
    simp only [subsetDerivative, s, Finset.sum_filter]
  simp_rw [heq]
  apply mean_sq_sum_orthonormal s (coefficient F) (fun S x => character (S \ K) x)
  intro S hS T hT
  rw [character_orthogonality]
  simp only [sdiff_injective_on_supersets K S T (Finset.mem_filter.mp hS).2
    (Finset.mem_filter.mp hT).2]

end Tusnady.Walsh
