import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
Elementary one-dimensional Brunn–Minkowski bound for compact sets.
This is the geometric ingredient in Ball's layer-cake proof of
Prékopa–Leindler (Lecture 5, Theorem 5.4). No higher-dimensional
Brunn–Minkowski or Prékopa–Leindler theorem is assumed.
-/

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace Tusnady.Prekopa

lemma volume_translate (A : Set ℝ) (b : ℝ) :
    volume ((fun x => x + b) '' A) = volume A := by
  rw [Set.image_add_right]
  simpa only [add_comm] using measure_preimage_add volume (-b) A

lemma volume_midpoint_image (A : Set ℝ) (b : ℝ) :
    volume ((fun x => (x + b) / 2) '' A) =
      ENNReal.ofReal (1 / 2 : ℝ) * volume A := by
  have himage : (fun x => (x + b) / 2) '' A =
      (1 / 2 : ℝ) • ((fun x => x + b) '' A) := by
    rw [← Set.image_smul, Set.image_image]
    congr 1
    funext x
    simp only [smul_eq_mul]
    ring
  rw [himage, Measure.addHaar_smul, volume_translate]
  simp

/-- Compact sets on the line satisfy the midpoint Brunn–Minkowski bound.
The target can be any set containing all the midpoints. -/
theorem compact_midpoint_measure_le {A B S : Set ℝ}
    (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hS : ∀ a ∈ A, ∀ b ∈ B, (a + b) / 2 ∈ S) :
    ENNReal.ofReal (1 / 2 : ℝ) * (volume A + volume B) ≤ volume S := by
  obtain ⟨a, ha, hmax⟩ := hA.exists_isGreatest hAn
  obtain ⟨b, hb, hmin⟩ := hB.exists_isLeast hBn
  let L := (fun x => (x + b) / 2) '' A
  let R := (fun y => (a + y) / 2) '' B
  have hLc : IsCompact L := hA.image (by fun_prop)
  have hRc : IsCompact R := hB.image (by fun_prop)
  have hinter : L ∩ R ⊆ {(a + b) / 2} := by
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, heq⟩⟩
    have hx' := hmax hx
    have hy' := hmin hy
    simp only [mem_singleton_iff]
    linarith
  have hnull : volume (L ∩ R) = 0 :=
    measure_mono_null hinter (measure_singleton _)
  have hunion : volume (L ∪ R) = volume L + volume R := by
    simpa only [hnull, add_zero] using measure_union_add_inter (μ := volume) L hRc.measurableSet
  have hsub : L ∪ R ⊆ S := by
    rintro z (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact hS x hx b hb
    · exact hS a ha y hy
  calc
    ENNReal.ofReal (1 / 2 : ℝ) * (volume A + volume B) =
        volume L + volume R := by
      dsimp [L, R]
      rw [volume_midpoint_image]
      have heq : (fun y : ℝ => (a + y) / 2) = (fun y => (y + a) / 2) := by
        funext y
        rw [add_comm]
      rw [heq, volume_midpoint_image, mul_add]
    _ = volume (L ∪ R) := hunion.symm
    _ ≤ volume S := measure_mono hsub

end Tusnady.Prekopa
