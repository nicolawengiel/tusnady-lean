import Tusnady.FrameMSSSelection
import Tusnady.External.RealRooted.MultivariateStability.MSSBound

/-! # Finite independent-vector MSS theorem

The output is an actual realization with strictly positive product
probability. Its matrix characteristic roots satisfy the optimized MSS
bound. All moment, splitness, root-selection and barrier steps are proved;
there is no supplied MSS, interlacing or partition hypothesis.
-/

noncomputable section
open Matrix Polynomial
open scoped BigOperators
namespace Tusnady.FrameMSS
open RealRooted.MixedCharacteristic

/-- Finite-support MSS, with a common finite outcome set, exactly sufficient
for the binary random vectors used by the frame partition construction. -/
theorem mss_roots_le {m n : ℕ} {κ : Type} [Fintype κ]
    (v : Fin m → κ → Fin n → ℝ) (p : Fin m → κ → ℝ)
    (hpn : ∀ i a, 0 ≤ p i a) (hp : ∀ i, ∑ a, p i a = 1)
    (hsum : ∑ i, secondMoment (v i) (p i) = 1)
    {ε : ℝ} (hε : 0 < ε)
    (htrace : ∀ i, (secondMoment (v i) (p i)).trace ≤ ε) :
    ∃ s : Fin m → κ, 0 < ∏ i, p i (s i) ∧
      ∀ r ∈ (∑ i, Matrix.vecMulVec (v i (s i)) (v i (s i))).charpoly.roots,
        r ≤ (1 + Real.sqrt ε) ^ 2 := by
  apply exists_product_positive_realization_roots_le v p hpn hp
  rw [expected, expectedCharpoly_eq_mixedCharacteristic _ _ _ hp]
  exact mixedCharacteristic_roots_le_one_add_sqrt_sq _
    (fun i => secondMoment_posSemidef _ _ (hpn i)) hsum hε htrace

end Tusnady.FrameMSS
