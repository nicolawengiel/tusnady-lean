import Tusnady.Main

/-!
# Explicit exact-cardinality witnesses and every real sign coloring

This corollary exposes the order of all quantifiers in the unchanged main
theorem. The positive constants precede N; the exact N-point family
precedes every real-valued sign coloring; the actual orthant parameter
may depend on the coloring. No balance condition is imposed.
-/

noncomputable section
open scoped BigOperators
namespace Tusnady
attribute [local instance] Classical.propDecidable

/-- Fully exposed witness version of Main.pdf Theorem 1.1 under exactly
the named literature bundle, for all real-valued ±1 colorings. The proved
`image_card_eq` explicitly identifies the number of different points. -/
theorem main_lower_bound_real_colorings (literature : Literature.Assumptions) :
    ∀ d : ℕ, 3 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∃ P : Fin N → Point d,
        Function.Injective P ∧ (Finset.univ.image P).card = N ∧
        ∀ χ : Fin N → ℝ, IsSignColoring χ →
          ∃ x : Point d,
            c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ)) ≤
              |∑ i ∈ trace P x, χ i| := by
  have hwitness := target_iff_witnessLowerBound.mp (main_lower_bound literature)
  intro d hd
  obtain ⟨c, hc, N₀, hN₀, hwitnessN⟩ := hwitness d hd
  refine ⟨c, hc, N₀, hN₀, ?_⟩
  intro N hN
  obtain ⟨P, hP, hall⟩ := hwitnessN N hN
  refine ⟨P, hP, image_card_eq P hP, ?_⟩
  intro χ hχ
  obtain ⟨b, hb⟩ := coloring_exhaustive χ hχ
  obtain ⟨x, hx⟩ := hall b
  refine ⟨x, ?_⟩
  have hsum : anchoredCount P b x = ∑ i ∈ trace P x, χ i := by
    unfold anchoredCount signedSum
    exact Finset.sum_congr rfl (fun i _ => hb i)
  rw [hsum] at hx
  exact hx

end Tusnady
