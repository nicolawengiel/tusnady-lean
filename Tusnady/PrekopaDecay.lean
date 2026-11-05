import Tusnady.PrekopaLayerCake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Structural conditions for the one-dimensional layer-cake theorem. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Tusnady.Prekopa

lemma compact_superlevels_of_tendsto_zero {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) (hlim : Tendsto f (cocompact X) (𝓝 0))
    {t : ℝ} (ht : 0 < t) : IsCompact {x | t ≤ f x} := by
  obtain ⟨K, hK, hsub⟩ := mem_cocompact'.mp (hlim.eventually_lt_const ht)
  apply hK.of_isClosed_subset (isClosed_le continuous_const hf)
  intro x hx
  exact hsub (by simpa only [mem_compl_iff, mem_setOf_eq, not_lt] using hx)

lemma positive_max_of_tendsto_zero {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) (hlim : Tendsto f (cocompact X) (𝓝 0))
    (hpos : ∃ x, 0 < f x) : ∃ xf, 0 < f xf ∧ ∀ x, f x ≤ f xf := by
  obtain ⟨x, hx⟩ := hpos
  obtain ⟨xf, hxf⟩ := hf.exists_forall_ge' x
    ((hlim.eventually_lt_const hx).mono (fun _ h => h.le))
  exact ⟨xf, hx.trans_le (hxf x), hxf⟩

/-- The continuous, positive, vanishing-at-infinity one-dimensional case. -/
theorem midpoint_integral_bound_of_decay {f g h : ℝ → ℝ}
    (hf : Integrable f) (hg : Integrable g) (hh : Integrable h)
    (hfc : Continuous f) (hgc : Continuous g)
    (hflim : Tendsto f (cocompact ℝ) (𝓝 0))
    (hglim : Tendsto g (cocompact ℝ) (𝓝 0))
    (hf0 : ∀ x, 0 < f x) (hg0 : ∀ x, 0 < g x) (hh0 : ∀ x, 0 ≤ h x)
    (hmid : ∀ x y, f x * g y ≤ (h ((x + y) / 2)) ^ 2) :
    (∫ x, f x) * (∫ x, g x) ≤ (∫ x, h x) ^ 2 :=
  midpoint_integral_bound_of_compact_superlevels hf hg hh
    (fun x => (hf0 x).le) (fun x => (hg0 x).le) hh0
    (fun _ ht => compact_superlevels_of_tendsto_zero hfc hflim ht)
    (fun _ ht => compact_superlevels_of_tendsto_zero hgc hglim ht)
    (positive_max_of_tendsto_zero hfc hflim ⟨0, hf0 0⟩)
    (positive_max_of_tendsto_zero hgc hglim ⟨0, hg0 0⟩) hmid

end Tusnady.Prekopa

namespace Tusnady.Prekopa

lemma tendsto_gaussian_at_cocompact {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ => Real.exp (-a * x ^ 2)) (cocompact ℝ) (𝓝 0) := by
  have hsq : Tendsto (fun x : ℝ => x ^ 2) (cocompact ℝ) atTop := by
    simpa only [Function.comp_def, Real.norm_eq_abs, sq_abs] using
      (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp
        (tendsto_norm_cocompact_atTop (E := ℝ))
  have hneg := tendsto_neg_atTop_atBot.comp (hsq.const_mul_atTop ha)
  simpa only [neg_mul] using Real.tendsto_exp_atBot.comp hneg

lemma tendsto_zero_of_gaussian_bound {f : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hf0 : ∀ x, 0 ≤ f x)
    (hfbound : ∀ x, f x ≤ C * Real.exp (-a * x ^ 2)) :
    Tendsto f (cocompact ℝ) (𝓝 0) := by
  apply squeeze_zero hf0 hfbound
  simpa using (tendsto_gaussian_at_cocompact ha).const_mul C

lemma integrable_of_scalar_gaussian_bound {f : ℝ → ℝ} {C a : ℝ}
    (ha : 0 < a) (hfm : AEStronglyMeasurable f volume)
    (hf0 : ∀ x, 0 ≤ f x) (hfbound : ∀ x, f x ≤ C * Real.exp (-a * x ^ 2)) :
    Integrable f := by
  apply ((integrable_exp_neg_mul_sq ha).const_mul C).mono' hfm
  exact Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hfbound x)

end Tusnady.Prekopa
