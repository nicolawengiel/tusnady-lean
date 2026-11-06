import Tusnady.CellFactorIntegrability

/-!
# Actual component expansion of mixed dyadic cell functions

Plain interval indicators are expanded by the proved ancestor-Haar formula;
modulated coordinates retain qI. Products distribute over the resulting
finite component type. The genuine high projection retains exactly the
components whose computed tensor levels reach h.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.DyadicFunctions Tusnady.Haar
open scoped BigOperators

/-- Modulated coordinates have one component. Plain coordinates have a
constant component and one component for each proper ancestor depth. -/
def ComponentIndex (j : ℕ) (modulated : Bool) : Type :=
  match modulated with
  | true => Unit
  | false => Option (Fin j)

instance componentIndex_fintype (j : ℕ) (m : Bool) : Fintype (ComponentIndex j m) := by
  cases m <;> dsimp [ComponentIndex] <;> infer_instance

instance componentIndex_decidableEq (j : ℕ) (m : Bool) : DecidableEq (ComponentIndex j m) := by
  cases m <;> dsimp [ComponentIndex] <;> infer_instance

/-- Deterministic ancestor signs, chosen from the already proved expansion. -/
def ancestorSigns (j : ℕ) (i : Fin (2^j)) : Fin j → ℝ :=
  Classical.choose (indicatorI_haar_expansion_unit j i)

lemma ancestorSigns_are_signs (j : ℕ) (i : Fin (2^j)) (b : Fin j) :
    ancestorSigns j i b = 1 ∨ ancestorSigns j i b = -1 :=
  (Classical.choose_spec (indicatorI_haar_expansion_unit j i)).1 b

lemma ancestorSigns_expansion (j : ℕ) (i : Fin (2^j)) (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) :
    indicatorI j i x = dyadicLength j + ∑ b : Fin j,
      ancestorSigns j i b*(dyadicLength j*(2:ℝ)^b.val)*ancestorHaar j i b x :=
  (Classical.choose_spec (indicatorI_haar_expansion_unit j i)).2 x hx

def componentFactor (H j : ℕ) (hj : j+2 < H) (i : Fin (2^j))
    (modulated : Bool) : ComponentIndex j modulated → Factor H := by
  cases modulated with
  | true => exact fun _ => .walsh j hj i 1
  | false =>
    exact fun b => match b with
      | none => .constant (dyadicLength j)
      | some b => .haar ⟨b.val, by omega⟩
          (Tusnady.Dyadic.ancestorIndex i b.val b.isLt.le)
          (ancestorSigns j i b*dyadicLength j*(2:ℝ)^b.val)

def cellCoordinateValue (j : ℕ) (i : Fin (2^j)) (modulated : Bool) (x : ℝ) : ℝ :=
  if modulated then qI j i x else indicatorI j i x

/-- The coordinate expansion is proved from the actual indicator expansion. -/
theorem coordinate_component_expansion (H j : ℕ) (hj : j+2 < H) (i : Fin (2^j))
    (modulated : Bool) (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) :
    cellCoordinateValue j i modulated x =
      ∑ b : ComponentIndex j modulated, factorValue (componentFactor H j hj i modulated b) x := by
  cases modulated with
  | true =>
    letI : Unique (ComponentIndex j true) := inferInstanceAs (Unique Unit)
    simp [componentFactor, cellCoordinateValue, factorValue]
  | false =>
    change indicatorI j i x = ∑ b : Option (Fin j), _
    rw [Fintype.sum_option]
    simpa only [componentFactor, factorValue, ancestorHaar, mul_assoc, add_comm] using
      ancestorSigns_expansion j i x hx

abbrev ComponentChoices {d : ℕ} (j : Fin d → ℕ) (m : Fin d → Bool) :=
  ∀ k, ComponentIndex (j k) (m k)

def cellComponentFactors {d H : ℕ} (j : Fin d → ℕ) (hj : ∀ k, j k+2 < H)
    (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool) (b : ComponentChoices j m) :
    Fin d → Factor H := fun k => componentFactor H (j k) (hj k) (I k) (m k) (b k)

def cellValue {d : ℕ} (j : Fin d → ℕ) (I : Tusnady.Dyadic.CellIndices j)
    (m : Fin d → Bool) (x : Fin d → ℝ) : ℝ :=
  ∏ k, cellCoordinateValue (j k) (I k) (m k) (x k)

/-- Actual finite component expansion, pointwise throughout the half-open cube. -/
theorem cell_component_expansion {d H : ℕ} (j : Fin d → ℕ) (hj : ∀ k, j k+2 < H)
    (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool) (x : Fin d → ℝ)
    (hx : ∀ k, x k ∈ Ico (0:ℝ) 1) :
    cellValue j I m x = ∑ b : ComponentChoices j m,
      tensorFactorValue (cellComponentFactors j hj I m b) x := by
  unfold cellValue
  calc
    _ = ∏ k, ∑ b : ComponentIndex (j k) (m k),
        factorValue (componentFactor H (j k) (hj k) (I k) (m k) b) (x k) := by
      apply Finset.prod_congr rfl
      intro k _
      exact coordinate_component_expansion H (j k) (hj k) (I k) (m k) (x k) (hx k)
    _ = _ := by
      rw [Fintype.prod_sum]
      rfl

/-- Actual L² cell vector, via its proved concrete finite component expansion. -/
def cellL2 {d H : ℕ} (j : Fin d → ℕ) (hj : ∀ k, j k+2 < H)
    (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool) : Lp ℝ 2 (cubeMeasure d) :=
  ∑ b : ComponentChoices j m, tensorFactorL2 (cellComponentFactors j hj I m b)

theorem cellL2_ae {d H : ℕ} (j : Fin d → ℕ) (hj : ∀ k, j k+2 < H)
    (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool) :
    cellL2 j hj I m =ᵐ[cubeMeasure d] cellValue j I m := by
  have hs := finite_sum_ae Finset.univ
    (fun b : ComponentChoices j m => tensorFactorL2 (cellComponentFactors j hj I m b))
    (fun b x => tensorFactorValue (cellComponentFactors j hj I m b) x)
    (fun b _ => tensorFactorL2_ae (cellComponentFactors j hj I m b))
  apply hs.trans
  filter_upwards [cubeMeasure_ae_unit d] with x hx
  exact (cell_component_expansion j hj I m x hx).symm

lemma highProjection_sum {d H : ℕ} {α : Type*} (h : ℕ) (s : Finset α)
    (v : α → Lp ℝ 2 (cubeMeasure d)) :
    highProjection d H h (∑ a ∈ s, v a) = ∑ a ∈ s, highProjection d H h (v a) := by
  unfold highProjection lowProjection projectionFor
  simp only [map_sum, Submodule.coe_sum, Finset.sum_sub_distrib]

lemma L2_integrable_upperBox {d : ℕ} (f : Lp ℝ 2 (cubeMeasure d)) (p : Tusnady.Point d)
    (hp : p ∈ Tusnady.UnitCube d) : IntegrableOn f (Tusnady.upperBox p) := by
  change Integrable f ((volume : Measure (Tusnady.Point d)).restrict (Tusnady.upperBox p))
  rw [← cubeMeasure_restrict_upperBox p hp]
  exact (MemLp.integrable (by norm_num : (1:ENNReal) ≤ 2) (Lp.memLp f)).integrableOn

/-- The actual primitive is linear on genuine finite sums of L² vectors. -/
lemma boxPrimitive_L2_sum {d : ℕ} {α : Type*} (s : Finset α)
    (v : α → Lp ℝ 2 (cubeMeasure d)) (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive ((∑ a ∈ s, v a) : Lp ℝ 2 (cubeMeasure d)) p =
      ∑ a ∈ s, Tusnady.boxPrimitive (v a) p := by
  have hs := finite_sum_ae s v (fun a x => v a x) (fun _ _ => Filter.EventuallyEq.rfl)
  rw [boxPrimitive_congr_cube_ae _ _ hs p hp]
  exact Tusnady.boxPrimitive_sum s (fun a x => v a x) p (fun a _ => L2_integrable_upperBox (v a) p hp)

/-- Exact retained component set, using the computed tensor level. -/
def retainedComponents {d H : ℕ} (h : ℕ) (j : Fin d → ℕ) (hj : ∀ k, j k+2 < H)
    (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool) : Finset (ComponentChoices j m) :=
  Finset.univ.filter (fun b => (h:ℤ) ≤ tensorFactorLevel (cellComponentFactors j hj I m b))

/-- The actual high cell primitive is exactly the finite sum of its retained
concrete components. There is no retained-component premise. -/
theorem boxPrimitive_high_cell_eq_sum {d H : ℕ} (h : ℕ) (j : Fin d → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool)
    (p : Tusnady.Point d) (hp : p ∈ Tusnady.UnitCube d) :
    Tusnady.boxPrimitive (highProjection d H h (cellL2 j hj I m)) p =
      ∑ b ∈ retainedComponents h j hj I m, tensorFactorPrimitive (cellComponentFactors j hj I m b) p := by
  unfold cellL2
  rw [highProjection_sum, boxPrimitive_L2_sum _ _ p hp]
  simp_rw [boxPrimitive_high_tensorFactor h _ p hp]
  simp only [retainedComponents, Finset.sum_filter]

/-- Integrated component bound. The remaining cell-location work is to
prove the explicit geometric bound B and bound the retained cardinality. -/
theorem integral_high_cell_le_card_sq {d H : ℕ} (h : ℕ) (j : Fin d → ℕ)
    (hj : ∀ k, j k+2 < H) (I : Tusnady.Dyadic.CellIndices j) (m : Fin d → Bool)
    (B : ℝ)
    (hB : ∀ b ∈ retainedComponents h j hj I m,
      (∏ k, factorPrimitiveMass (cellComponentFactors j hj I m b k)) ≤ B) :
    (∫ p, Tusnady.boxPrimitive (highProjection d H h (cellL2 j hj I m)) p^2 ∂cubeMeasure d) ≤
      ((retainedComponents h j hj I m).card:ℝ)^2*B := by
  have hae : (fun p => Tusnady.boxPrimitive (highProjection d H h (cellL2 j hj I m)) p^2) =ᵐ[cubeMeasure d]
      (fun p => (∑ b ∈ retainedComponents h j hj I m,
        tensorFactorPrimitive (cellComponentFactors j hj I m b) p)^2) := by
    filter_upwards [cubeMeasure_ae_UnitCube d] with p hp
    rw [boxPrimitive_high_cell_eq_sum h j hj I m p hp]
  rw [integral_congr_ae hae]
  apply integral_sum_sq_le_card_sq (cubeMeasure d) (retainedComponents h j hj I m)
    (fun b => tensorFactorPrimitive (cellComponentFactors j hj I m b))
    (fun b _ => tensorFactorPrimitive_memLp (cellComponentFactors j hj I m b)) B
  intro b hb
  rw [integral_tensorFactorPrimitive_sq]
  exact hB b hb

end Tusnady.Cell
