import Tusnady.Integrated.Statements
import Tusnady.PlanarWei.LowerBound
import Tusnady.MainUnconditional

/-! The lower bound in every dimension at least two: Wei's proved planar
case and the preserved proved higher-dimensional case. -/
noncomputable section
namespace Tusnady.Integrated

theorem lower_bound : LowerBound := by
  intro d hd
  by_cases htwo : d = 2
  · subst d
    obtain ⟨c, hc, h⟩ := PlanarWei.planar_lower_bound
    exact ⟨c, hc, 2, le_rfl, fun N hN => h N (by omega)⟩
  · obtain ⟨c, hc, N₀, _, h⟩ := Tusnady.main_lower_bound_unconditional d (by omega)
    exact ⟨c, hc, max 2 N₀, le_max_left _ _,
      fun N hN => h N ((le_max_right _ _).trans hN)⟩

/-- Exactly N distinct points resist every real sign coloring; the orthant
may depend on the coloring. No balance condition is imposed. -/
theorem lower_bound_real_colorings :
    ∀ d : ℕ, 2 ≤ d → ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∃ P : Fin N → Point d, Function.Injective P ∧
        ∀ χ : Fin N → ℝ, IsSignColoring χ → ∃ x : Point d,
          c * targetGrowth d N ≤ |realAnchoredCount P χ x| := by
  intro d hd
  obtain ⟨c, hc, N₀, hN₀, hbound⟩ := lower_bound d hd
  refine ⟨c, hc, N₀, hN₀, fun N hN => ?_⟩
  obtain ⟨P, hP, heq⟩ := exists_worst_configuration (d := d) (by omega) N
  refine ⟨P, hP, (le_pointDiscrepancy_iff_real_colorings P _).mp ?_⟩
  simpa only [heq] using hbound N hN

end Tusnady.Integrated
