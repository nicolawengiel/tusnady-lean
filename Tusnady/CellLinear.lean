import Tusnady.CellPolynomial

/-! Exact degree-one identification and the cubic remainder of W. -/
noncomputable section
open scoped BigOperators
namespace Tusnady.Witness
variable {d h : ℕ}

def linearShapeCoefficient (j : Fin d) (theta : ℝ) (r : Dyadic.Shape d h) : ℝ :=
  (1/4:ℝ)*Walsh.coefficient
    (Walsh.smoothedBlock theta : Walsh.Cube (ShapesInBlock j (shapeBlockIndex j r)) → ℝ)
    {⟨r,rfl⟩}

lemma shapeCoefficient_singleton_eq_linear (j : Fin d) (theta : ℝ) (r : BlockShape j h) :
    shapeCoefficient j theta {r} = linearShapeCoefficient j theta r.2.val := by
  rcases r with ⟨a,⟨r,hr⟩⟩
  have ha : a = shapeBlockIndex j r := Subtype.ext (Fin.ext hr.symm)
  subst a
  rw [shapeCoefficient_singleton]
  rfl

/-- The singleton portion of the proved expansion is exactly the W_lin
already defined with actual shell coefficients in TestFunction.lean. -/
theorem singleton_sum_eq_linearTestFunction (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) :
    (∑ r : BlockShape j h, shapeCoefficient j theta {r} * layer r.2.val u x) =
      linearTestFunction j theta u x := by
  classical
  simp_rw [shapeCoefficient_singleton_eq_linear]
  have hsum := (blockShapeEquiv (h := h) j).sum_comp
    (fun r => linearShapeCoefficient j theta r * layer r u x)
  change (∑ r : BlockShape j h,
    linearShapeCoefficient j theta ((blockShapeEquiv j) r) *
      layer ((blockShapeEquiv j) r) u x) = _
  rw [hsum]
  unfold linearTestFunction
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro r _
  unfold layer
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  change linearShapeCoefficient j theta r * (u ⟨r,c⟩ * qShell ⟨r,c⟩ x) =
    linearShapeCoefficient j theta r * u ⟨r,c⟩ * qShell ⟨r,c⟩ x
  ring

lemma sum_singleton_terms {α : Type*} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) :
    (∑ S : Finset α, if S.card = 1 then f S else 0) = ∑ a : α, f {a} := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun a _ => {a})
  · intro a _
    simp
  · intro a _ b _ hab
    exact Finset.singleton_injective hab
  · intro S hS
    have hcard : S.card = 1 := (Finset.mem_filter.mp hS).2
    obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
    exact ⟨a, Finset.mem_univ a, rfl⟩
  · intro a _
    rfl

/-- Full explicit cubic remainder identity. No unspecified polynomial
or higher-degree remainder is inserted as a hypothesis. -/
theorem testFunction_sub_linear_expansion (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) :
    testFunction j theta u x - linearTestFunction j theta u x =
      ∑ S : Finset (BlockShape j h), if 3 ≤ S.card then
        shapeCoefficient j theta S * ∏ r ∈ S, layer r.2.val u x else 0 := by
  classical
  let f : Finset (BlockShape j h) → ℝ := fun S =>
    shapeCoefficient j theta S * ∏ r ∈ S, layer r.2.val u x
  have hsmall (S : Finset (BlockShape j h)) (hS : S.card < 3) (hn : S.card ≠ 1) : f S = 0 := by
    have heven : Even S.card := by
      have hs : S.card = 0 ∨ S.card = 2 := by omega
      rcases hs with hs | hs <;> rw [hs] <;> norm_num
    simp only [f, shapeCoefficient_even_eq_zero j theta S heven, zero_mul]
  have hsplit : (∑ S : Finset (BlockShape j h), f S) =
      (∑ S : Finset (BlockShape j h), if S.card = 1 then f S else 0) +
      ∑ S : Finset (BlockShape j h), if 3 ≤ S.card then f S else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S _
    by_cases h1 : S.card = 1
    · rw [if_pos h1, if_neg (by omega), add_zero]
    · by_cases h3 : 3 ≤ S.card
      · rw [if_neg h1, if_pos h3, zero_add]
      · rw [if_neg h1, if_neg h3, hsmall S (by omega) h1, add_zero]
  rw [testFunction_shapeExpansion]
  change (∑ S : Finset (BlockShape j h), f S)-linearTestFunction j theta u x = _
  rw [hsplit, sum_singleton_terms]
  have hlin : (∑ r : BlockShape j h, f {r}) = linearTestFunction j theta u x := by
    simpa only [f, Finset.prod_singleton] using singleton_sum_eq_linearTestFunction j theta u x
  rw [hlin]
  ring

theorem testFunction_sub_linear_cellExpansion (j : Fin d) (theta : ℝ)
    (u : Shell d h → ℝ) (x : Point d) :
    testFunction j theta u x - linearTestFunction j theta u x =
      ∑ S : Finset (BlockShape j h), ∑ c : CellChoice S, if 3 ≤ S.card then
        shapeCoefficient j theta S * cellMonomial S c u * cellFunction S c x else 0 := by
  classical
  rw [testFunction_sub_linear_expansion]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : 3 ≤ S.card
  · simp only [if_pos hS]
    rw [product_layers_expansion, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    ring
  · simp only [if_neg hS, Finset.sum_const_zero]

end Tusnady.Witness
