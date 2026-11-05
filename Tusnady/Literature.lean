import Tusnady.EntropyDensityConditional
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Named external assumptions (not global axioms)

The named external theorems and the two classical entropy/transform facts
explicitly cited in Main.pdf are listed here. These definitions do not
assert their truth. `Assumptions`
would be an explicit input of a completed conditional main theorem.
No original construction, remainder bound or entropy correlation is a field.
Precise sources and the remaining library interfaces: docs/LITERATURE.md.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace Tusnady.Literature

abbrev Vector (n : ℕ) := Fin n → ℝ

def standardGaussian (n : ℕ) : Measure (Vector n) :=
  Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- Linear images of independent standard Gaussian coordinates, allowing
singular and zero covariance matrices. No nonsingularity is assumed. -/
def CenteredGaussian (n : ℕ) (μ : Measure (Vector n)) : Prop :=
  ∃ k : ℕ, ∃ B : Matrix (Fin n) (Fin k) ℝ,
    μ = (standardGaussian k).map (fun z i => ∑ j, B i j * z j)

/-- Šidák 1967, Corollary 1; Main.pdf Theorem A.
Measures are ENNReal probabilities; all thresholds are strictly positive. -/
def Sidak : Prop :=
  ∀ (n : ℕ) (μ : Measure (Vector n)), CenteredGaussian n μ →
    ∀ c : Fin n → ℝ, (∀ i, 0 < c i) →
      (∏ i, μ {x | |x i| ≤ c i}) ≤ μ {x | ∀ i, |x i| ≤ c i}

/-- Anderson 1955, Theorem 1 / Corollary 2, including the degenerate Gaussian
extension for closed convex symmetric sets discussed in Main.pdf §2.4. -/
def Anderson : Prop :=
  ∀ (n : ℕ) (μ : Measure (Vector n)), CenteredGaussian n μ →
    ∀ K : Set (Vector n), IsClosed K → Convex ℝ K →
      (∀ x : Vector n, x ∈ K ↔ -x ∈ K) →
      ∀ c : Vector n, μ {x | x - c ∈ K} ≤ μ K

/-- The t=1 special case of Limonova--Temlyakov, Theorem 1.1,
JMAA 515 (2022), 126457; arXiv:2009.10789v2, p. 3.
Orthonormality is stated by actual integrals; all functions are measurable
and pairwise products integrable. Repetitions among sampling points are
allowed. Making them distinct and controlling weights are our own tasks. -/
def Sampling : Prop :=
  ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧
    ∀ (ambient D : ℕ), 0 < D →
    ∀ Ω : Set (Vector ambient), Ω.Nonempty →
    ∀ μ : Measure Ω, IsProbabilityMeasure μ →
    ∀ u : Fin D → Ω → ℝ,
      (∀ i, Measurable (u i)) →
      (∀ i j, Integrable (fun x => u i x * u j x) μ) →
      (∀ i j, (∫ x, u i x * u j x ∂μ) = if i = j then 1 else 0) →
      (∀ x, (∑ i, |u i x| ^ 2) ≤ (D : ℝ)) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C₁ * (D : ℝ) ∧
        ∃ ξ : Fin m → Ω, ∀ a : Fin D → ℝ,
          C₂ * (∫ x, |∑ i, a i * u i x| ^ 2 ∂μ) ≤
            (1 / (m : ℝ)) * ∑ j, |∑ i, a i * u i (ξ j)| ^ 2 ∧
          (1 / (m : ℝ)) * ∑ j, |∑ i, a i * u i (ξ j)| ^ 2 ≤
            C₃ * (∫ x, |∑ i, a i * u i x| ^ 2 ∂μ)

/-- Cover--Thomas, Elements of Information Theory, 2nd ed., Theorem 8.6.2
(p. 253), with conditional differential entropy as defined in §8.4.

This is only the classical chain identity for the *actual* conditional
densities. Its finiteness input is explicit and is proved separately for
the constructed bounded-density systems. No correlation bound is assumed. -/
def ConditionalEntropyChainIdentity : Prop :=
  ∀ (M : ℕ) (f : (Fin M → ℝ) → ℝ) (s : Tusnady.ConditionalDensitySystem M f),
    (∀ j, Integrable (s.entropyAt j) s.law) →
      (∑ j, ∫ z, s.entropyAt j z ∂s.law) = Tusnady.densityEntropy volume f

/-- Rosenblatt 1952: the actual successive conditional CDFs map an
absolutely continuous joint probability law to product uniform measure.
The [-1,1] normalization is the affine image of the original [0,1] form.
The input system records actual prefix-dependent scalar densities and the
general disintegration identity; its existence is proved, not assumed. -/
def RosenblattUniform : Prop :=
  ∀ (M : ℕ) (f : (Fin M → ℝ) → ℝ) (s : Tusnady.ConditionalDensitySystem M f),
    Measure.map s.cdfTransform s.law = Measure.pi
      (fun _ : Fin M => ProbabilityTheory.cond (volume : Measure ℝ) (Set.Icc (-1 : ℝ) 1))

/-- The declared external theorem bundle. There is intentionally no
inhabitant supplied, and no global `axiom` declaration. -/
structure Assumptions : Prop where
  sidak : Sidak
  anderson : Anderson
  sampling : Sampling
  entropyChain : ConditionalEntropyChainIdentity
  rosenblatt : RosenblattUniform

end Tusnady.Literature
