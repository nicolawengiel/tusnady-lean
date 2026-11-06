import Tusnady.Upper.Ehrhard.PolyhedralApproximation
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Compactness.Lindelof

/-!
# Countable outer halfspace approximation of closed convex sets

Strict Hahn--Banach separation and the Lindelöf property of a separable Hilbert
space give countably many closed halfspaces whose intersection is exactly K.
Finite initial intersections decrease to K, with eventual pointwise equality
of their indicators.  Boundary points belong to every approximating set.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace OAI.GaussianPropeller.ConvexApproximation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E]

/-- Every closed convex set is an intersection of countably many actual affine
halfspaces. The result includes the empty and the universal set. -/
theorem exists_countable_slack_representation (K : Set E) (hKclosed : IsClosed K)
    (hKconvex : Convex ℝ K) :
    ∃ v : ℕ → E, ∃ b : ℕ → ℝ,
      ∀ x, x ∈ K ↔ ∀ n, 0 ≤ b n + ⟪v n, x⟫ := by
  classical
  let I := {p : StrongDual ℝ E × ℝ // ∀ x ∈ K, p.1 x ≤ p.2}
  letI : Nonempty I := ⟨⟨(0, 0), by intro x hx; simp⟩⟩
  let U : I → Set E := fun p => {x | p.val.2 < p.val.1 x}
  have hUopen : ∀ i, IsOpen (U i) := fun i => isOpen_lt continuous_const i.val.1.continuous
  have hcover : Kᶜ ⊆ ⋃ i, U i := by
    intro x hx
    obtain ⟨f, a, hfa, hax⟩ := geometric_hahn_banach_closed_point hKconvex hKclosed hx
    exact mem_iUnion.mpr ⟨⟨(f, a), fun y hy => (hfa y hy).le⟩, hax⟩
  obtain ⟨g, hg⟩ := (HereditarilyLindelofSpace.isLindelof Kᶜ).indexed_countable_subcover U hUopen hcover
  refine ⟨fun n => -(InnerProductSpace.toDual ℝ E).symm (g n).val.1,
    fun n => (g n).val.2, ?_⟩
  intro x
  simp only [inner_neg_left, InnerProductSpace.toDual_symm_apply]
  constructor
  · intro hx n
    have h := (g n).property x hx
    linarith
  · intro hx
    by_contra hxK
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hg hxK)
    change (g n).val.2 < (g n).val.1 x at hn
    have h := hx n
    linarith

/-- Nonempty finite index sets are used, matching the smooth-CDF approximation. -/
def outerSet (v : ℕ → E) (b : ℕ → ℝ) (n : ℕ) : Set E :=
  AffineSoftMin.slackSet (fun i : Fin (n + 1) => v i.val) (fun i => b i.val)

lemma mem_outerSet (v : ℕ → E) (b : ℕ → ℝ) (n : ℕ) (x : E) :
    x ∈ outerSet v b n ↔ ∀ i : Fin (n + 1), 0 ≤ b i.val + ⟪v i.val, x⟫ := Iff.rfl

lemma outerSet_antitone (v : ℕ → E) (b : ℕ → ℝ) : Antitone (outerSet v b) := by
  intro m n hmn x hx i
  exact hx ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hmn)⟩

lemma isClosed_outerSet (v : ℕ → E) (b : ℕ → ℝ) (n : ℕ) :
    IsClosed (outerSet v b n) := by
  have heq : outerSet v b n = ⋂ i : Fin (n + 1), {x : E | 0 ≤ b i.val + ⟪v i.val, x⟫} := by
    ext x
    simp [outerSet, AffineSoftMin.slackSet]
  rw [heq]
  apply isClosed_iInter
  intro i
  exact isClosed_le continuous_const (show Continuous (fun x : E => b i.val + ⟪v i.val, x⟫) by fun_prop)

lemma convex_outerSet (v : ℕ → E) (b : ℕ → ℝ) (n : ℕ) :
    Convex ℝ (outerSet v b n) := by
  intro x hx y hy a c ha hc hac i
  have hi := hx i
  have hj := hy i
  have hia := mul_nonneg ha hi
  have hjc := mul_nonneg hc hj
  change 0 ≤ b i.val + ⟪v i.val, a • x + c • y⟫
  simp only [inner_add_right, inner_smul_right]
  have heq := congrArg (fun r : ℝ => r * b i.val) hac
  dsimp only at hi hj hia hjc heq
  nlinarith [heq]

lemma iInter_outerSet (v : ℕ → E) (b : ℕ → ℝ) :
    (⋂ n, outerSet v b n) = {x : E | ∀ n, 0 ≤ b n + ⟪v n, x⟫} := by
  ext x
  simp only [mem_iInter, mem_outerSet, mem_setOf_eq]
  constructor
  · intro h n
    exact h n ⟨n, Nat.lt_succ_self n⟩
  · intro h n i
    exact h i.val

lemma subset_outerSet (K : Set E) (v : ℕ → E) (b : ℕ → ℝ)
    (hrep : ∀ x, x ∈ K ↔ ∀ n, 0 ≤ b n + ⟪v n, x⟫) (n : ℕ) :
    K ⊆ outerSet v b n := by
  intro x hx i
  exact (hrep x).mp hx i.val

/-- Indicator equality is eventually exact at every point, including boundary points. -/
lemma indicator_outerSet_eventually_eq (K : Set E) (v : ℕ → E) (b : ℕ → ℝ)
    (hrep : ∀ x, x ∈ K ↔ ∀ n, 0 ≤ b n + ⟪v n, x⟫) (x : E) :
    ∀ᶠ n : ℕ in atTop, (outerSet v b n).indicator (fun _ => (1 : ℝ)) x =
      K.indicator (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : x ∈ K
  · exact Eventually.of_forall (fun n => by simp [hx, subset_outerSet K v b hrep n hx])
  · have hnot : ¬ ∀ n, 0 ≤ b n + ⟪v n, x⟫ := fun h => hx ((hrep x).mpr h)
    push_neg at hnot
    obtain ⟨i, hi⟩ := hnot
    filter_upwards [eventually_ge_atTop i] with n hn
    have hxnot : x ∉ outerSet v b n := by
      intro hxn
      exact (not_le.mpr hi) (hxn ⟨i, Nat.lt_succ_of_le hn⟩)
    simp [hx, hxnot]

lemma indicator_outerSet_tendsto (K : Set E) (v : ℕ → E) (b : ℕ → ℝ)
    (hrep : ∀ x, x ∈ K ↔ ∀ n, 0 ≤ b n + ⟪v n, x⟫) (x : E) :
    Tendsto (fun n : ℕ => (outerSet v b n).indicator (fun _ => (1 : ℝ)) x) atTop
      (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) :=
by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [indicator_outerSet_eventually_eq K v b hrep x] with n hn
  exact hn.symm

/-- A closed convex set has nested finite-halfspace outer approximations with
pointwise convergence everywhere, without a boundary-null assumption. -/
theorem exists_outer_approximation (K : Set E) (hKclosed : IsClosed K)
    (hKconvex : Convex ℝ K) :
    ∃ v : ℕ → E, ∃ b : ℕ → ℝ,
      (∀ n, K ⊆ outerSet v b n) ∧ Antitone (outerSet v b) ∧
      (⋂ n, outerSet v b n) = K ∧
      ∀ x, Tendsto (fun n : ℕ => (outerSet v b n).indicator (fun _ => (1 : ℝ)) x) atTop
        (𝓝 (K.indicator (fun _ => (1 : ℝ)) x)) := by
  obtain ⟨v, b, hrep⟩ := exists_countable_slack_representation K hKclosed hKconvex
  refine ⟨v, b, subset_outerSet K v b hrep, outerSet_antitone v b, ?_,
    indicator_outerSet_tendsto K v b hrep⟩
  rw [iInter_outerSet]
  ext x
  exact (hrep x).symm

section Measure
variable [MeasurableSpace E] [BorelSpace E]

/-- Dominated convergence of actual probabilities, valid also for singular
Gaussian affine maps. It requires no information about the boundary of K. -/
theorem measure_outerSet_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set E) (hKclosed : IsClosed K)
    (v : ℕ → E) (b : ℕ → ℝ)
    (hrep : ∀ x, x ∈ K ↔ ∀ n, 0 ≤ b n + ⟪v n, x⟫)
    (F : X → E) (hF : Measurable F) :
    Tendsto (fun n : ℕ => μ.real (F ⁻¹' outerSet v b n)) atTop
      (𝓝 (μ.real (F ⁻¹' K))) := by
  classical
  have hm (n : ℕ) : MeasurableSet (F ⁻¹' outerSet v b n) :=
    (isClosed_outerSet v b n).measurableSet.preimage hF
  have hkm : MeasurableSet (F ⁻¹' K) := hKclosed.measurableSet.preimage hF
  have hlim := tendsto_integral_of_dominated_convergence (μ := μ)
    (bound := fun _ : X => (1 : ℝ))
    (F := fun n : ℕ => (F ⁻¹' outerSet v b n).indicator (fun _ => (1 : ℝ)))
    (f := (F ⁻¹' K).indicator (fun _ => (1 : ℝ)))
    (fun n => (measurable_const.indicator (hm n)).aestronglyMeasurable)
    (integrable_const _) (fun n => ae_of_all _ (fun z => by
      by_cases hz : F z ∈ outerSet v b n <;> simp [hz]))
    (ae_of_all _ (fun z => indicator_outerSet_tendsto K v b hrep (F z)))
  have hi (n : ℕ) : (∫ z, (F ⁻¹' outerSet v b n).indicator (fun _ => (1 : ℝ)) z ∂μ) =
      μ.real (F ⁻¹' outerSet v b n) := integral_indicator_one (hm n)
  have hk : (∫ z, (F ⁻¹' K).indicator (fun _ => (1 : ℝ)) z ∂μ) = μ.real (F ⁻¹' K) :=
    integral_indicator_one hkm
  simpa only [hi, hk] using hlim

end Measure
end OAI.GaussianPropeller.ConvexApproximation
