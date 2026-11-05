import Tusnady.Literature
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.NormNum

/-!
# The finite cover and union-bound step of Main.pdf Lemma 7.1

The events below are actual subsets and their masses are actual measures.
The two local inputs are the rounding cover and domination of every
translated event by the centered event. Neither input is declared to be a
literature result. The input lower bound for the cube is the consequence
of Sidak and the one-dimensional variance comparison used in Main.pdf.

This module proves the finite counting/measure-transfer step, not the
entire Gaussian-cover lemma. It proves the linear-image Gaussian fact and
the Sidak/Anderson applications, but it does not prove the hereditary-
discrepancy rounding construction or the one-dimensional variance comparison.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace Tusnady.GaussianCover

/-- The cube `[-r,r]^k`, including boundary points. -/
def cube (k : ℕ) (r : ℝ) : Set (Fin k → ℝ) :=
  {x | ∀ j, |x j| ≤ r}

/-- The fixed one-dimensional probability `P(|g| ≤ 1)` for a standard
Gaussian, denoted by `p₀` in Lemma 7.1. It is independent of `n`, `m`, and `D`. -/
def standardUnitMass : ℝ≥0∞ :=
  ProbabilityTheory.gaussianReal 0 1 {x : ℝ | |x| ≤ 1}

/-- Every two-coloring gives one of the exactly `2^n` sign vectors. -/
def signVector {n : ℕ} (σ : Fin n → Bool) : Fin n → ℝ :=
  fun i => if σ i then 1 else -1

/-- The event `A x ∈ [-2D,2D]^m`. -/
def centeredEvent {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ) : Set (Fin n → ℝ) :=
  {x | A x ∈ cube m (2 * D)}

/-- The event `A x ∈ A σ + [-2D,2D]^m`. -/
def translatedEvent {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ)
    (σ : Fin n → Bool) : Set (Fin n → ℝ) :=
  {x | A x - A (signVector σ) ∈ cube m (2 * D)}

theorem cube_isClosed (k : ℕ) (r : ℝ) : IsClosed (cube k r) := by
  simp only [cube, Set.setOf_forall]
  exact isClosed_iInter fun j =>
    isClosed_le ((continuous_apply j).abs) continuous_const

theorem cube_convex (k : ℕ) (r : ℝ) : Convex ℝ (cube k r) := by
  have h : cube k r = Set.pi Set.univ (fun _ : Fin k => Set.Icc (-r) r) := by
    ext x
    simp only [cube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc, abs_le]
  rw [h]
  exact convex_pi fun _ _ => convex_Icc _ _

theorem cube_symmetric (k : ℕ) (r : ℝ) (x : Fin k → ℝ) :
    x ∈ cube k r ↔ -x ∈ cube k r := by
  simp [cube]

theorem centeredEvent_isClosed {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ) :
    IsClosed (centeredEvent A D) :=
  (cube_isClosed m (2 * D)).preimage A.continuous_of_finiteDimensional

theorem translatedEvent_isClosed {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ)
    (σ : Fin n → Bool) : IsClosed (translatedEvent A D σ) :=
  (cube_isClosed m (2 * D)).preimage
    (A.continuous_of_finiteDimensional.sub continuous_const)

theorem signVector_count (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

theorem signVector_injective (n : ℕ) :
    Function.Injective (@signVector n) := by
  intro σ τ h
  funext i
  have hi := congrFun h i
  cases hσ : σ i <;> cases hτ : τ i <;>
    simp [signVector, hσ, hτ] at hi ⊢
  all_goals norm_num at hi

/-- Genuine finite subadditivity over the `2^n` translated rounding events.
This holds for any measure; no Gaussian assumption or probability
normalization is needed for this step. -/
theorem cube_mass_le_sign_count_mul_center {n m : ℕ}
    (μ : Measure (Fin n → ℝ))
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ)
    (hcover : cube n 1 ⊆ ⋃ σ : Fin n → Bool, translatedEvent A D σ)
    (htranslate : ∀ σ : Fin n → Bool,
      μ (translatedEvent A D σ) ≤ μ (centeredEvent A D)) :
    μ (cube n 1) ≤ (2 : ℝ≥0∞) ^ n * μ (centeredEvent A D) := by
  calc
    μ (cube n 1) ≤ μ (⋃ σ : Fin n → Bool, translatedEvent A D σ) :=
      measure_mono hcover
    _ ≤ ∑ σ : Fin n → Bool, μ (translatedEvent A D σ) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ _σ : Fin n → Bool, μ (centeredEvent A D) :=
      Finset.sum_le_sum fun σ _ => htranslate σ
    _ = (2 : ℝ≥0∞) ^ n * μ (centeredEvent A D) := by
      simp [Finset.sum_const, nsmul_eq_mul, Nat.cast_pow]

/-- The first displayed lower bound in the proof of Lemma 7.1 after
rounding, Sidak and Anderson have supplied the visible local inputs. -/
theorem cube_lower_le_sign_count_mul_center {n m : ℕ}
    (μ : Measure (Fin n → ℝ))
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ) (p₀ : ℝ≥0∞)
    (hcover : cube n 1 ⊆ ⋃ σ : Fin n → Bool, translatedEvent A D σ)
    (htranslate : ∀ σ : Fin n → Bool,
      μ (translatedEvent A D σ) ≤ μ (centeredEvent A D))
    (hcube : p₀ ^ n ≤ μ (cube n 1)) :
    p₀ ^ n ≤ (2 : ℝ≥0∞) ^ n * μ (centeredEvent A D) :=
  hcube.trans (cube_mass_le_sign_count_mul_center μ A D hcover htranslate)

/-- Division by the exact number of sign vectors yields the desired
`(p₀/2)^n` bound. No positivity assumption on `p₀` is hidden. -/
theorem center_mass_lower_of_cover {n m : ℕ}
    (μ : Measure (Fin n → ℝ))
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ) (p₀ : ℝ≥0∞)
    (hcover : cube n 1 ⊆ ⋃ σ : Fin n → Bool, translatedEvent A D σ)
    (htranslate : ∀ σ : Fin n → Bool,
      μ (translatedEvent A D σ) ≤ μ (centeredEvent A D))
    (hcube : p₀ ^ n ≤ μ (cube n 1)) :
    (p₀ / 2) ^ n ≤ μ (centeredEvent A D) := by
  have h := cube_lower_le_sign_count_mul_center μ A D p₀ hcover htranslate hcube
  have htwo : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have htop : (2 : ℝ≥0∞) ^ n ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
  have hdiv : p₀ ^ n / (2 : ℝ≥0∞) ^ n ≤ μ (centeredEvent A D) :=
    (ENNReal.div_le_iff' htwo htop).2 h
  simpa [div_eq_mul_inv, mul_pow, ENNReal.inv_pow] using hdiv

/-- Real probabilities for a probability measure, obtained without any
informal conversion from extended-real division. -/
theorem center_real_mass_lower_of_cover {n m : ℕ}
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ) (p₀ : ℝ≥0∞)
    (hcover : cube n 1 ⊆ ⋃ σ : Fin n → Bool, translatedEvent A D σ)
    (htranslate : ∀ σ : Fin n → Bool,
      μ (translatedEvent A D σ) ≤ μ (centeredEvent A D))
    (hcube : p₀ ^ n ≤ μ (cube n 1)) :
    (p₀.toReal / 2) ^ n ≤ μ.real (centeredEvent A D) := by
  have h := center_mass_lower_of_cover μ A D p₀ hcover htranslate hcube
  have hreal := ENNReal.toReal_mono (measure_ne_top μ _) h
  simpa [measureReal_def] using hreal

/-- The cube-mass input follows directly from the actual Sidak statement
and a common lower bound for all one-coordinate slab probabilities. -/
theorem cube_mass_lower_of_sidak {n : ℕ}
    (hSidak : Literature.Sidak) (μ : Measure (Fin n → ℝ))
    (hGaussian : Literature.CenteredGaussian n μ) (p₀ : ℝ≥0∞)
    (hmarginal : ∀ i : Fin n, p₀ ≤ μ {x | |x i| ≤ 1}) :
    p₀ ^ n ≤ μ (cube n 1) := by
  calc
    p₀ ^ n = ∏ _i : Fin n, p₀ := by simp
    _ ≤ ∏ i : Fin n, μ {x | |x i| ≤ 1} :=
      Finset.prod_le_prod' fun i _ => hmarginal i
    _ ≤ μ (cube n 1) :=
      hSidak n μ hGaussian (fun _ => 1) (fun _ => by norm_num)

/-- A linear image of the actual matrix-defined centered Gaussian law
is centered Gaussian, including singular laws. This structural fact is
proved here rather than added to the literature assumptions. -/
theorem centeredGaussian_linear_image {n m : ℕ}
    (μ : Measure (Fin n → ℝ)) (hGaussian : Literature.CenteredGaussian n μ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    Literature.CenteredGaussian m (μ.map A) := by
  rcases hGaussian with ⟨k, B, rfl⟩
  let C : Matrix (Fin m) (Fin k) ℝ := fun i j => A (fun l => B l j) i
  refine ⟨k, C, ?_⟩
  have hB : Measurable (fun z : Fin k → ℝ => fun i : Fin n => ∑ j, B i j * z j) := by
    apply measurable_pi_lambda
    intro i
    exact Finset.measurable_sum _ fun j _ => measurable_const.mul (measurable_pi_apply j)
  rw [Measure.map_map A.continuous_of_finiteDimensional.measurable hB]
  congr 1
  funext z i
  have hv : (fun l : Fin n => ∑ j, B l j * z j) =
      ∑ j : Fin k, z j • (fun l : Fin n => B l j) := by
    ext l
    simp [Finset.sum_apply, mul_comm]
  change A (fun l => ∑ j, B l j * z j) i = ∑ j, C i j * z j
  rw [hv, map_sum]
  simp [C, Finset.sum_apply, mul_comm]

/-- Direct application of the named Anderson input to the actual image
law of `A`. The image law's Gaussian property is still an explicit local
input in this intermediate theorem. -/
theorem translated_mass_le_of_anderson {n m : ℕ}
    (hAnderson : Literature.Anderson) (μ : Measure (Fin n → ℝ))
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ)
    (hImageGaussian : Literature.CenteredGaussian m (μ.map A))
    (σ : Fin n → Bool) :
    μ (translatedEvent A D σ) ≤ μ (centeredEvent A D) := by
  have hA : Measurable A := A.continuous_of_finiteDimensional.measurable
  have hK : MeasurableSet (cube m (2 * D)) := (cube_isClosed _ _).measurableSet
  have hT : MeasurableSet {y : Fin m → ℝ | y - A (signVector σ) ∈ cube m (2 * D)} :=
    ((cube_isClosed m (2 * D)).preimage (continuous_id.sub continuous_const)).measurableSet
  have h := hAnderson m (μ.map A) hImageGaussian (cube m (2 * D))
    (cube_isClosed _ _) (cube_convex _ _) (cube_symmetric _ _) (A (signVector σ))
  rw [Measure.map_apply hA hT, Measure.map_apply hA hK] at h
  exact h

/-- Composition of the proved union bound with both named literature
inputs. The rounding cover and the Gaussian marginal comparison are
visible local obligations; this is not the full Lemma 7.1. -/
theorem center_mass_lower_of_sidak_anderson_cover {n m : ℕ}
    (hSidak : Literature.Sidak) (hAnderson : Literature.Anderson)
    (μ : Measure (Fin n → ℝ))
    (hGaussian : Literature.CenteredGaussian n μ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ) (p₀ : ℝ≥0∞)
    (hcover : cube n 1 ⊆ ⋃ σ : Fin n → Bool, translatedEvent A D σ)
    (hmarginal : ∀ i : Fin n, p₀ ≤ μ {x | |x i| ≤ 1}) :
    (p₀ / 2) ^ n ≤ μ (centeredEvent A D) :=
  center_mass_lower_of_cover μ A D p₀ hcover
    (translated_mass_le_of_anderson hAnderson μ A D
      (centeredGaussian_linear_image μ hGaussian A))
    (cube_mass_lower_of_sidak hSidak μ hGaussian p₀ hmarginal)

/-- The exact fixed `p₀` used in Main.pdf. The remaining marginal
comparison is not silently replaced by a free constant. -/
theorem center_mass_lower_standard_of_cover {n m : ℕ}
    (hSidak : Literature.Sidak) (hAnderson : Literature.Anderson)
    (μ : Measure (Fin n → ℝ))
    (hGaussian : Literature.CenteredGaussian n μ)
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (D : ℝ)
    (hcover : cube n 1 ⊆ ⋃ σ : Fin n → Bool, translatedEvent A D σ)
    (hmarginal : ∀ i : Fin n, standardUnitMass ≤ μ {x | |x i| ≤ 1}) :
    (standardUnitMass / 2) ^ n ≤ μ (centeredEvent A D) :=
  center_mass_lower_of_sidak_anderson_cover hSidak hAnderson μ hGaussian
    A D standardUnitMass hcover hmarginal

end Tusnady.GaussianCover
