import Tusnady.CellGeometry

/-!
# Actual one-coordinate products on ancestor families

The depth separation by three is used here, rather than assumed as a
product rule. Coarser qI factors are proved constant on the deepest real
interval. The parity of the number of deepest factors then determines
qI versus the plain interval indicator.
-/

set_option autoImplicit false
noncomputable section
namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.Dyadic Tusnady.DyadicFunctions Tusnady.Haar Tusnady.Witness
open scoped BigOperators

variable {d h : ℕ}

def sidePeak (S : Finset (Shape d h)) (k : Fin d) (r : S) : Prop := r.val.depth k = join S k

instance sidePeak_decidable (S : Finset (Shape d h)) (k : Fin d) (r : S) : Decidable (sidePeak S k r) :=
  inferInstanceAs (Decidable (r.val.depth k = join S k))

def peakCount (S : Finset (Shape d h)) (k : Fin d) : ℕ :=
  (Finset.univ.filter (sidePeak S k)).card

def peakModulated (S : Finset (Shape d h)) (k : Fin d) : Bool := decide (Odd (peakCount S k))

def sideAncestor (S : Finset (Shape d h)) (k : Fin d) (I : Fin (2^(join S k))) (r : S) :
    Fin (2^(r.val.depth k)) := ancestorIndex I (r.val.depth k) (depth_le_join S r.property k)

def sideProduct (S : Finset (Shape d h)) (k : Fin d) (I : Fin (2^(join S k))) (x : ℝ) : ℝ :=
  ∏ r : S, qI (r.val.depth k) (sideAncestor S k I r) x

def coordinateSign (S : Finset (Shape d h)) (k : Fin d) (I : Fin (2^(join S k))) : ℝ :=
  ∏ r : S, if sidePeak S k r then 1 else
    qI (r.val.depth k) (sideAncestor S k I r) (dyadicLeft (join S k) I)

lemma dyadicLeft_mem (a : ℕ) (i : Fin (2^a)) : dyadicLeft a i ∈ dyadicInterval a i := by
  constructor
  · exact le_rfl
  · change dyadicLeft a i < dyadicLeft a i+dyadicLength a
    linarith [dyadicLength_pos a]

lemma qI_ancestor_same (a b : ℕ) (hab : a ≤ b) (i : Fin (2^b)) (heq : a = b) (x : ℝ) :
    qI a (ancestorIndex i a hab) x = qI b i x := by
  subst a
  rw [ancestorIndex_self]

/-- Every lower-depth factor is constant on the deepest actual interval. -/
lemma nonpeak_qI_constant (S : Finset (Shape d h)) (k : Fin d) (I : Fin (2^(join S k)))
    (r : S) (hr : ¬ sidePeak S k r) (x : ℝ) (hx : x ∈ dyadicInterval (join S k) I) :
    qI (r.val.depth k) (sideAncestor S k I r) x =
      qI (r.val.depth k) (sideAncestor S k I r) (dyadicLeft (join S k) I) := by
  have hle := depth_le_join S r.property k
  have hne : r.val.depth k ≠ join S k := hr
  have hlt : r.val.depth k < join S k := lt_of_le_of_ne hle hne
  have hsep : r.val.depth k+3 ≤ join S k := by
    obtain ⟨a,ha⟩ := r.val.three_dvd_depth k
    obtain ⟨b,hb⟩ := three_dvd_join S k
    omega
  obtain ⟨value,hvalue⟩ := qI_constant_on_finer (r.val.depth k) (join S k) hsep
    (sideAncestor S k I r) I
  exact (hvalue hx).trans (hvalue (dyadicLeft_mem (join S k) I)).symm

/-- All constant factors are genuine signs, since the chosen point lies
inside every real ancestor interval. -/
theorem coordinateSign_abs (S : Finset (Shape d h)) (k : Fin d) (I : Fin (2^(join S k))) :
    |coordinateSign S k I| = 1 := by
  unfold coordinateSign
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro r _
  by_cases hr : sidePeak S k r
  · rw [if_pos hr]
    norm_num
  · rw [if_neg hr]
    have hpoint := dyadicInterval_subset_ancestor (depth_le_join S r.property k) I
      (dyadicLeft_mem (join S k) I)
    change dyadicLeft (join S k) I ∈ dyadicInterval (r.val.depth k) (sideAncestor S k I r) at hpoint
    have hq := abs_q (dyadicLeft (r.val.depth k) (sideAncestor S k I r))
      (dyadicLength (r.val.depth k)) (dyadicLeft (join S k) I) (dyadicLength_pos _)
    change _ = (dyadicInterval (r.val.depth k) (sideAncestor S k I r)).indicator
      (fun _ => (1:ℝ)) (dyadicLeft (join S k) I) at hq
    rw [Set.indicator_of_mem hpoint] at hq
    exact hq

lemma sign_pow_by_parity (q : ℝ) (n : ℕ) (hq : |q| = 1) :
    q^n = if Odd n then q else 1 := by
  have hsq : q^2 = 1 := by rw [← sq_abs, hq]; norm_num
  have hmul : (q-1)*(q+1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hmul with hp | hm
  · have hq1 : q = 1 := by linarith
    simp [hq1]
  · have hqm : q = -1 := by linarith
    rw [hqm]
    by_cases hn : Odd n
    · rw [if_pos hn]
      exact hn.neg_one_pow
    · rw [if_neg hn]
      have he : Even n := (Nat.even_or_odd n).resolve_right hn
      exact he.neg_one_pow

lemma sideProduct_on_cell (S : Finset (Shape d h)) (k : Fin d) (I : Fin (2^(join S k)))
    (x : ℝ) (hx : x ∈ dyadicInterval (join S k) I) :
    sideProduct S k I x = coordinateSign S k I *
      (qI (join S k) I x)^(peakCount S k) := by
  classical
  have hfactor : ∀ r : S, qI (r.val.depth k) (sideAncestor S k I r) x =
      (if sidePeak S k r then qI (join S k) I x else 1) *
      (if sidePeak S k r then 1 else
        qI (r.val.depth k) (sideAncestor S k I r) (dyadicLeft (join S k) I)) := by
    intro r
    by_cases hr : sidePeak S k r
    · rw [if_pos hr, if_pos hr, mul_one]
      exact qI_ancestor_same _ _ (depth_le_join S r.property k) I hr x
    · rw [if_neg hr, if_neg hr, one_mul]
      exact nonpeak_qI_constant S k I r hr x hx
  have hprod : (∏ r : S, if sidePeak S k r then qI (join S k) I x else 1) =
      (qI (join S k) I x)^(peakCount S k) := by
    rw [← Finset.prod_filter]
    simp [peakCount]
  unfold sideProduct
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, hprod]
  unfold coordinateSign
  ring

lemma sideProduct_zero_outside (S : Finset (Shape d h)) (hS : S.Nonempty) (k : Fin d)
    (I : Fin (2^(join S k))) (x : ℝ) (hx : x ∉ dyadicInterval (join S k) I) :
    sideProduct S k I x = 0 := by
  obtain ⟨r,hr,hmax⟩ := Finset.exists_mem_eq_sup S hS (fun r => r.depth k)
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨r,hr⟩ : S))
  change qI (r.depth k) (ancestorIndex I (r.depth k) _) x = 0
  rw [qI_ancestor_same _ _ (depth_le_join S hr k) I hmax.symm x]
  exact qI_zero_outside (join S k) I x hx

/-- Full actual coordinate product rule, including its support and all
half-open boundaries. This is the one-dimensional core of Lemma 4.2(b). -/
theorem sideProduct_factorization (S : Finset (Shape d h)) (hS : S.Nonempty) (k : Fin d)
    (I : Fin (2^(join S k))) (x : ℝ) :
    sideProduct S k I x = coordinateSign S k I *
      cellCoordinateValue (join S k) I (peakModulated S k) x := by
  classical
  by_cases hx : x ∈ dyadicInterval (join S k) I
  · have hq : |qI (join S k) I x| = 1 := by
      have h := abs_q (dyadicLeft (join S k) I) (dyadicLength (join S k)) x (dyadicLength_pos _)
      change _ = (dyadicInterval (join S k) I).indicator (fun _ => (1:ℝ)) x at h
      rw [Set.indicator_of_mem hx] at h
      exact h
    rw [sideProduct_on_cell S k I x hx, sign_pow_by_parity _ _ hq]
    unfold cellCoordinateValue peakModulated
    by_cases ho : Odd (peakCount S k) <;> simp [ho, indicatorI, hx]
  · rw [sideProduct_zero_outside S hS k I x hx]
    unfold cellCoordinateValue
    have hq := qI_zero_outside (join S k) I x hx
    have hi : indicatorI (join S k) I x = 0 := Set.indicator_of_notMem hx _
    simp [hq, hi]

end Tusnady.Cell

namespace Tusnady.Cell
open MeasureTheory Set
open Tusnady.Dyadic Tusnady.DyadicFunctions Tusnady.Haar Tusnady.Witness
open scoped BigOperators
variable {d h : ℕ}

def cellSign (S : Finset (Shape d h)) (I : CellIndices (join S)) : ℝ :=
  ∏ k, coordinateSign S k (I k)

theorem cellSign_abs (S : Finset (Shape d h)) (I : CellIndices (join S)) : |cellSign S I| = 1 := by
  unfold cellSign
  rw [Finset.abs_prod]
  simp only [coordinateSign_abs, Finset.prod_const_one]

/-- Lemma 4.2(b), as an exact identity of the actual real functions on all
of real space, with support and half-open boundary behavior included. -/
theorem familyProduct_factorization (S : Finset (Shape d h)) (hS : S.Nonempty)
    (I : CellIndices (join S)) (x : Tusnady.Point d) :
    familyProduct S (boxFamilyFromCell S I) x =
      cellSign S I * cellValue (join S) I (peakModulated S) x := by
  classical
  unfold familyProduct qShell familyShell
  change (∏ r : S, ∏ k : Fin d, qI (r.val.depth k) (sideAncestor S k (I k) r) (x k)) = _
  rw [Finset.prod_comm]
  calc
    _ = ∏ k : Fin d, sideProduct S k (I k) (x k) := rfl
    _ = ∏ k : Fin d, coordinateSign S k (I k)*
        cellCoordinateValue (join S k) (I k) (peakModulated S k) (x k) := by
      apply Finset.prod_congr rfl
      intro k _
      exact sideProduct_factorization S hS k (I k) (x k)
    _ = _ := by rw [Finset.prod_mul_distrib]; rfl

lemma peakCount_eq (S : Finset (Shape d h)) (k : Fin d) :
    peakCount S k = (S.filter (fun r => r.depth k = join S k)).card := by
  classical
  calc
    _ = ∑ r : S, if r.val.depth k = join S k then 1 else 0 := by
      unfold peakCount sidePeak
      simp
    _ = ∑ r ∈ S, if r.depth k = join S k then 1 else 0 :=
      Finset.sum_coe_sort S (fun r => if r.depth k = join S k then (1:ℕ) else 0)
    _ = _ := by simp

/-- Odd multiplicity on the first coordinate levels implies the first
join coordinate remains modulated. This is the precise parity condition
used by the later admissibility argument. -/
theorem peakModulated_eq_true (S : Finset (Shape d h)) (hS : S.Nonempty) (k : Fin d)
    (hodd : ∀ a, (∃ r ∈ S, r.depth k = a) → Odd ((S.filter (fun r => r.depth k = a)).card)) :
    peakModulated S k = true := by
  obtain ⟨r,hr,hmax⟩ := Finset.exists_mem_eq_sup S hS (fun r => r.depth k)
  have ho := hodd (join S k) ⟨r,hr,hmax.symm⟩
  simp only [peakModulated, decide_eq_true_eq, peakCount_eq]
  exact ho

end Tusnady.Cell
