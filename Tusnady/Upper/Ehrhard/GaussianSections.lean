import Tusnady.Upper.Ehrhard.GaussianBase
import Tusnady.Upper.PrefixFoldGeometry
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual Gaussian product decomposition and vertical fold sections

The Gaussian is the transported product measure defined in `GaussianBase`.
Its coordinate decomposition and section formulas are proved, with no Gaussian
measure hypothesis.  The vertical section identity uses the concrete closed
fold from `PrefixFoldGeometry` and requires no convexity assumption.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace OAI.GaussianPropeller.GaussianSections

variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin k)
local notation "E'" => EuclideanSpace ℝ (Fin (k + 1))

def front (z : E') : E := WithLp.toLp 2 (fun i => z i.castSucc)
def last (z : E') : ℝ := z (Fin.last k)
def append (y : E) (t : ℝ) : E' := WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) t)
def split (z : E') : E × ℝ := (front z, last z)

@[simp] theorem front_apply (z : E') (i : Fin k) : front z i = z i.castSucc := rfl
@[simp] theorem append_castSucc (y : E) (t : ℝ) (i : Fin k) : append y t i.castSucc = y i := by
  simp [append]
@[simp] theorem append_last (y : E) (t : ℝ) : last (append y t) = t := by simp [last, append]
@[simp] theorem front_append (y : E) (t : ℝ) : front (append y t) = y := by ext i; simp
@[simp] theorem append_front_last (z : E') : append (front z) (last z) = z := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [last, append]
  · simp

theorem continuous_front : Continuous (front : E' → E) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).comp
    (continuous_pi fun i => PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) i.castSucc)

theorem continuous_last : Continuous (last : E' → ℝ) :=
  PiLp.continuous_apply 2 (fun _ : Fin (k + 1) => ℝ) (Fin.last k)

theorem continuous_append : Continuous (fun p : E × ℝ => append p.1 p.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (k + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using continuous_snd
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) j).comp continuous_fst

theorem continuous_split : Continuous (split : E' → E × ℝ) :=
  continuous_front.prodMk continuous_last

private theorem toLp_measurePreserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) (gaussianMeasure ι) :=
  ⟨(PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable, rfl⟩

private theorem ofLp_measurePreserving (ι : Type*) [Fintype ι] :
    MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ ι → (ι → ℝ))
      (gaussianMeasure ι) (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  refine ⟨(PiLp.continuous_ofLp 2 (fun _ : ι => ℝ)).measurable, ?_⟩
  rw [gaussianMeasure, Measure.map_map
    (PiLp.continuous_ofLp 2 (fun _ : ι => ℝ)).measurable
    (PiLp.continuous_toLp 2 (fun _ : ι => ℝ)).measurable]
  simp [Function.comp_def]

/-- The finite Gaussian law decomposes into the first `k` coordinates and the
last scalar coordinate, in that order. -/
theorem split_measurePreserving : MeasurePreserving (split : E' → E × ℝ)
    (gaussianMeasure (Fin (k + 1))) ((gaussianMeasure (Fin k)).prod (gaussianReal 0 1)) := by
  have hraw := measurePreserving_piFinSuccAbove
    (fun _ : Fin (k + 1) => gaussianReal 0 1) (Fin.last k)
  have hswap := Measure.measurePreserving_swap.comp hraw
  have hlift := ((toLp_measurePreserving (Fin k)).prod (MeasurePreserving.id (gaussianReal 0 1))).comp hswap
  have h := hlift.comp (ofLp_measurePreserving (Fin (k + 1)))
  convert h using 1
  funext z
  apply Prod.ext
  · ext i
    simp [split, front, Function.comp_def, MeasurableEquiv.piFinSuccAbove, Fin.init]
  · simp [split, last, Function.comp_def, MeasurableEquiv.piFinSuccAbove]

theorem split_law : (gaussianMeasure (Fin (k + 1))).map (split : E' → E × ℝ) =
    (gaussianMeasure (Fin k)).prod (gaussianReal 0 1) := split_measurePreserving.map_eq

def verticalSection (K : Set E') (y : E) : Set ℝ := {t | append y t ∈ K}

theorem measurableSet_verticalSection {K : Set E'} (hK : MeasurableSet K) (y : E) :
    MeasurableSet (verticalSection K y) :=
  hK.preimage (continuous_append.comp (continuous_const.prodMk continuous_id)).measurable

theorem isClosed_verticalSection {K : Set E'} (hK : IsClosed K) (y : E) :
    IsClosed (verticalSection K y) :=
  hK.preimage (continuous_append.comp (continuous_const.prodMk continuous_id))

theorem measurable_verticalSection_mass {K : Set E'} (hK : MeasurableSet K) :
    Measurable (fun y : E => (gaussianReal 0 1) (verticalSection K y)) :=
  measurable_measure_prodMk_left (hK.preimage continuous_append.measurable)

/-- Actual Gaussian Fubini formula in nonnegative extended-real form. -/
theorem gaussianMeasure_sections (K : Set E') (hK : MeasurableSet K) :
    (gaussianMeasure (Fin (k + 1))) K =
      ∫⁻ y : E, (gaussianReal 0 1) (verticalSection K y) ∂gaussianMeasure (Fin k) := by
  have hpre : MeasurableSet ((fun p : E × ℝ => append p.1 p.2) ⁻¹' K) :=
    hK.preimage continuous_append.measurable
  calc
    (gaussianMeasure (Fin (k + 1))) K =
        ((gaussianMeasure (Fin (k + 1))).map (split : E' → E × ℝ))
          ((fun p : E × ℝ => append p.1 p.2) ⁻¹' K) := by
      rw [Measure.map_apply continuous_split.measurable hpre]
      congr 1
      ext z
      simp [split]
    _ = ((gaussianMeasure (Fin k)).prod (gaussianReal 0 1))
        ((fun p : E × ℝ => append p.1 p.2) ⁻¹' K) := by rw [split_law]
    _ = _ := by rw [Measure.prod_apply hpre]; rfl

/-- The same Fubini identity in the real-valued convention used by the upper
bound and by the fold-monotonicity statement. -/
theorem gaussianMeasure_real_sections (K : Set E') (hK : MeasurableSet K) :
    (gaussianMeasure (Fin (k + 1))).real K =
      ∫ y : E, (gaussianReal 0 1).real (verticalSection K y) ∂gaussianMeasure (Fin k) := by
  rw [measureReal_def, gaussianMeasure_sections K hK]
  symm
  exact integral_toReal (measurable_verticalSection_mass hK).aemeasurable
    (ae_of_all _ (fun _ => measure_lt_top _ _))

def axis (r : ℝ) : E' := append 0 r

@[simp] theorem append_sub_axis (y : E) (s r : ℝ) :
    append y s - axis r = append y (s - r) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [append, axis]

@[simp] theorem append_add_axis (y : E) (s r : ℝ) :
    append y s + axis r = append y (s + r) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [append, axis]

@[simp] theorem append_add_smul_axis (y : E) (s q r : ℝ) :
    append y s + q • axis r = append y (s + q * r) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [append, axis, smul_eq_mul]

/-- The concrete multidimensional fold acts separately on every vertical
fiber when its direction is the last coordinate axis. -/
theorem verticalSection_signingFold (K : Set E') (r : ℝ) (y : E) :
    verticalSection (Tusnady.Upper.signingFold (axis r) K) y =
      Tusnady.Upper.signingFold r (verticalSection K y) := by
  ext t
  constructor
  · intro ht
    obtain ⟨c, q, hm, hp, hq, heq⟩ :=
      (Tusnady.Upper.mem_signingFold_iff K (axis r) (append y t)).1 ht
    have hfront : front c = y := by
      ext i
      have h := congrArg (fun z : E' => z i.castSucc) heq
      simpa [append, axis] using h.symm
    have hcrepr : c = append y (last c) := by
      rw [← hfront]
      exact (append_front_last c).symm
    apply (Tusnady.Upper.mem_signingFold_iff (verticalSection K y) r t).2
    refine ⟨last c, q, ?_, ?_, hq, ?_⟩
    · change append y (last c - r) ∈ K
      rw [← append_sub_axis, ← hcrepr]
      exact hm
    · change append y (last c + r) ∈ K
      rw [← append_add_axis, ← hcrepr]
      exact hp
    · simpa [last, append, axis, smul_eq_mul] using congrArg last heq
  · intro ht
    obtain ⟨c, q, hm, hp, hq, heq⟩ :=
      (Tusnady.Upper.mem_signingFold_iff (verticalSection K y) r t).1 ht
    change append y t ∈ Tusnady.Upper.signingFold (axis r) K
    apply (Tusnady.Upper.mem_signingFold_iff K (axis r) (append y t)).2
    refine ⟨append y c, q, ?_, ?_, hq, ?_⟩
    · rw [append_sub_axis]
      exact hm
    · rw [append_add_axis]
      exact hp
    · rw [append_add_smul_axis]
      simpa only [smul_eq_mul] using congrArg (append y) heq

end OAI.GaussianPropeller.GaussianSections
