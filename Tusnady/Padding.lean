import Tusnady.Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Padding with distinct invisible points

The geometric last step of Main.pdf, §7, pp. 27–28. Padding points really
lie in (1,2)^d; they are distinct and cannot enter any lower orthant whose
corner lies in [0,1]^d. The restriction on corners in the premise is explicit.
-/
noncomputable section
open scoped BigOperators
namespace Tusnady
attribute [local instance] Classical.propDecidable

/-- The `i`-th new point, on the diagonal of the open cube (1,2)^d. -/
def paddingPoint (d m : ℕ) (i : Fin m) : Point d :=
  fun _ => 1 + ((i.val : ℝ) + 1) / ((m : ℝ) + 1)

theorem paddingPoint_bounds (i : Fin m) (j : Fin d) :
    1 < paddingPoint d m i j ∧ paddingPoint d m i j < 2 := by
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hi : (i.val : ℝ) < m := by exact_mod_cast i.isLt
  have hpos : 0 < ((i.val : ℝ) + 1) / ((m : ℝ) + 1) :=
    div_pos (by positivity) hm
  have hlt : ((i.val : ℝ) + 1) / ((m : ℝ) + 1) < 1 :=
    (div_lt_one hm).2 (by linarith)
  constructor <;> dsimp [paddingPoint] <;> linarith

theorem paddingPoint_injective (hd : 0 < d) (m : ℕ) :
    Function.Injective (paddingPoint d m) := by
  intro i j hij
  have h := congrFun hij (⟨0, hd⟩ : Fin d)
  change 1 + ((i.val : ℝ) + 1) / ((m : ℝ) + 1) =
    1 + ((j.val : ℝ) + 1) / ((m : ℝ) + 1) at h
  have hm : (m : ℝ) + 1 ≠ 0 := by positivity
  have hf : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 :=
    (div_left_inj' hm).1 (add_left_cancel h)
  apply Fin.ext
  exact_mod_cast (add_right_cancel hf)

def paddedFamily (P : Fin k → Point d) (m : ℕ) : Fin k ⊕ Fin m → Point d :=
  Sum.elim P (paddingPoint d m)

theorem paddedFamily_injective (hd : 0 < d) (P : Fin k → Point d)
    (hP : Function.Injective P) (hPc : ∀ i, P i ∈ OpenUnitCube d) (m : ℕ) :
    Function.Injective (paddedFamily P m) := by
  intro a b hab
  cases a with
  | inl i =>
    cases b with
    | inl j => exact congrArg Sum.inl (hP hab)
    | inr j =>
      have hlo := (hPc i (⟨0, hd⟩ : Fin d)).2
      have hhi := (paddingPoint_bounds j (⟨0, hd⟩ : Fin d)).1
      have heq := congrFun hab (⟨0, hd⟩ : Fin d)
      change P i ⟨0, hd⟩ = paddingPoint d m j ⟨0, hd⟩ at heq
      linarith
  | inr i =>
    cases b with
    | inl j =>
      have hlo := (hPc j (⟨0, hd⟩ : Fin d)).2
      have hhi := (paddingPoint_bounds i (⟨0, hd⟩ : Fin d)).1
      have heq := congrFun hab (⟨0, hd⟩ : Fin d)
      change paddingPoint d m i ⟨0, hd⟩ = P j ⟨0, hd⟩ at heq
      linarith
    | inr j => exact congrArg Sum.inr (paddingPoint_injective hd m hab)

theorem paddingPoint_not_anchored (hd : 0 < d) (i : Fin m) (x : Point d)
    (hx : x ∈ UnitCube d) : paddingPoint d m i ∉ Anchored x := by
  intro hi
  have hhi := (paddingPoint_bounds i (⟨0, hd⟩ : Fin d)).1
  have hlo := hi (⟨0, hd⟩ : Fin d)
  have hx1 := (hx (⟨0, hd⟩ : Fin d)).2
  linarith

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem anchoredCount_eq_sum (P : ι → Point d) (χ : ι → Bool) (x : Point d) :
    anchoredCount P χ x = ∑ i, if P i ∈ Anchored x then sign (χ i) else 0 := by
  classical
  simp [anchoredCount, signedSum, trace, Finset.sum_filter]

theorem anchoredCount_reindex (e : κ ≃ ι) (P : ι → Point d)
    (χ : ι → Bool) (x : Point d) :
    anchoredCount (P ∘ e) (χ ∘ e) x = anchoredCount P χ x := by
  classical
  simp only [anchoredCount_eq_sum, Function.comp_apply]
  exact e.sum_comp (fun i => if P i ∈ Anchored x then sign (χ i) else 0)

theorem anchoredCount_padded (hd : 0 < d) (P : Fin k → Point d)
    (χ : Fin k ⊕ Fin m → Bool) (x : Point d) (hx : x ∈ UnitCube d) :
    anchoredCount (paddedFamily P m) χ x =
      anchoredCount P (fun i => χ (Sum.inl i)) x := by
  classical
  simp only [anchoredCount_eq_sum, Fintype.sum_sum_type, paddedFamily, Sum.elim_inl,
    Sum.elim_inr]
  simp [paddingPoint_not_anchored hd _ x hx]
  rfl

/-- Every coloring of the padded set restricts to a coloring of the old set.
This theorem makes no claim about the existence of the original witness. -/
theorem padding_preserves_lower_bound (hd : 0 < d) (P : Fin k → Point d)
    (hP : Function.Injective P) (hPc : ∀ i, P i ∈ OpenUnitCube d)
    {a : ℝ}
    (hdisc : ∀ χ : Fin k → Bool, ∃ x : Point d,
      x ∈ UnitCube d ∧ a ≤ |anchoredCount P χ x|) (m : ℕ) :
    ∃ Q : Fin (k + m) → Point d, Function.Injective Q ∧
      ∀ χ : Fin (k + m) → Bool, ∃ x : Point d,
        x ∈ UnitCube d ∧ a ≤ |anchoredCount Q χ x| := by
  let e : Fin k ⊕ Fin m ≃ Fin (k + m) := finSumFinEquiv
  let Q := paddedFamily P m ∘ e.symm
  refine ⟨Q, (paddedFamily_injective hd P hP hPc m).comp e.symm.injective, ?_⟩
  intro χ
  obtain ⟨x, hx, ha⟩ := hdisc (fun i => χ (e (Sum.inl i)))
  refine ⟨x, hx, ?_⟩
  have hreindex := anchoredCount_reindex e Q χ x
  have hcomp : Q ∘ e = paddedFamily P m := by
    funext i
    simp [Q]
  rw [hcomp, anchoredCount_padded hd P (χ ∘ e) x hx] at hreindex
  rw [← hreindex]
  exact ha

/-- Padding works for every prescribed final cardinality N, with no repeated
points and without changing the lower bound. -/
theorem padding_to_exact_cardinality (hd : 0 < d) (P : Fin k → Point d)
    (hP : Function.Injective P) (hPc : ∀ i, P i ∈ OpenUnitCube d)
    {a : ℝ}
    (hdisc : ∀ χ : Fin k → Bool, ∃ x : Point d,
      x ∈ UnitCube d ∧ a ≤ |anchoredCount P χ x|) (hkN : k ≤ N) :
    ∃ Q : Fin N → Point d, Function.Injective Q ∧
      ∀ χ : Fin N → Bool, ∃ x : Point d,
        x ∈ UnitCube d ∧ a ≤ |anchoredCount Q χ x| := by
  have h := padding_preserves_lower_bound hd P hP hPc hdisc (N - k)
  have hcard : k + (N - k) = N := Nat.add_sub_of_le hkN
  rw [hcard] at h
  exact h

end Tusnady
