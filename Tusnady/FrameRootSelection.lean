import Tusnady.FrameRootSegment
import Mathlib.Algebra.Polynomial.BigOperators

/-! Finite weighted largest-root selection from actual splitness of all
convex combinations. The conclusion has no common-interleaver premise. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.FrameRootSelection
open Polynomial Set Filter
open scoped BigOperators Topology NNReal
variable {ι : Type*} [Fintype ι]

/-- Actual finite weighted polynomial mean. -/
def mean (w : ι → ℝ) (p : ι → ℝ[X]) : ℝ[X] := ∑ i, w i • p i

@[simp] lemma mean_coeff (w : ι → ℝ) (p : ι → ℝ[X]) (j : ℕ) :
    (mean w p).coeff j = ∑ i, w i*(p i).coeff j := by
  simp [mean]

@[simp] lemma mean_eval (w : ι → ℝ) (p : ι → ℝ[X]) (x : ℝ) :
    (mean w p).eval x = ∑ i, w i*(p i).eval x := by
  rw [mean,Polynomial.eval_finset_sum]
  simp

lemma mean_monic_degree (w : ι → ℝ) (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀ i, (p i).Monic) (hpd : ∀ i, (p i).natDegree = d) (hw : ∑ i, w i = 1) :
    (mean w p).Monic ∧ (mean w p).natDegree = d := by
  classical
  have hle : (mean w p).natDegree ≤ d :=
    natDegree_sum_le_of_forall_le _ _ (fun i _ => (natDegree_smul_le _ _).trans (hpd i).le)
  have hc : (mean w p).coeff d = 1 := by
    simp only [mean,finset_sum_coeff,coeff_smul,smul_eq_mul]
    convert hw using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← hpd i,(hp i).coeff_natDegree,mul_one]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one d hle hc,
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; norm_num))⟩

lemma mean_segment_single [DecidableEq ι] (w : ι → ℝ) (p : ι → ℝ[X]) (i : ι) (t : ℝ) :
    mean (fun j => (1-t)*w j+if j=i then t else 0) p = segment (mean w p) (p i) t := by
  classical
  ext j
  simp [mean,segment,add_mul,Finset.sum_add_distrib,Finset.mul_sum,ite_mul,mul_assoc]

lemma eval_pos_of_roots_lt {p : ℝ[X]} (hp : p.Monic) (hs : p.Splits)
    {x : ℝ} (hbelow : ∀ r ∈ p.roots, r < x) : 0 < p.eval x := by
  rw [hs.eval_eq_prod_roots,hp.leadingCoeff,one_mul]
  apply Multiset.prod_pos
  intro y hy
  obtain ⟨r,hr,rfl⟩ := Multiset.mem_map.mp hy
  exact sub_pos.mpr (hbelow r hr)

/-- Threshold form of finite weighted MSS root selection. Every member is
monic of the same degree, and every genuine convex combination splits.
Some strictly positive-weight member has all roots below any upper bound
for the roots of the actual weighted parent polynomial. -/
theorem exists_pos_weight_roots_le (w : ι → ℝ) (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀ i, (p i).Monic) (hpd : ∀ i, (p i).natDegree = d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    (hsplit : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) → (∑ i, a i = 1) →
      (mean a p).Splits)
    (R : ℝ) (hparent : ∀ r ∈ (mean w p).roots, r ≤ R) :
    ∃ i, 0 < w i ∧ ∀ r ∈ (p i).roots, r ≤ R := by
  classical
  by_contra hnone
  have hbad : ∀ i, 0 < w i → ∃ r, r ∈ (p i).roots ∧ R < r := by
    intro i hi
    have hh : ¬ ∀ r ∈ (p i).roots, r ≤ R := fun hr => hnone ⟨i,hi,hr⟩
    push_neg at hh
    exact hh
  have hwpos : ∃ i, 0 < w i := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_nonpos (s:=Finset.univ) (fun i _ => hn i)
    rw [hwsum] at hh
    norm_num at hh
  let S : Finset ι := Finset.univ.filter (fun i => 0 < w i)
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hwpos
    exact ⟨i,by simp [S,hi]⟩
  letI : Nonempty S := by
    obtain ⟨i,hi⟩ := hS
    exact ⟨⟨i,hi⟩⟩
  have hbr : ∀ i : S, ∃ r, r ∈ (p i).roots ∧ R < r := fun i =>
    hbad i (Finset.mem_filter.mp i.property).2
  choose r hr using hbr
  obtain ⟨i,_,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset S) r Finset.univ_nonempty
  let x : ℝ := (R+r i)/2
  have hRx : R < x := by dsimp [x]; linarith [(hr i).2]
  have hxr : x < r i := by dsimp [x]; linarith [(hr i).2]
  have hmean := mean_monic_degree w p hp hpd hwsum
  have hmeanbelow : ∀ s ∈ (mean w p).roots, s < x :=
    fun s hs => (hparent s hs).trans_lt hRx
  have hmeanpos := eval_pos_of_roots_lt hmean.1 (hsplit w hw hwsum) hmeanbelow
  have hex : ∃ j, 0 < w j*(p j).eval x := by
    by_contra hn
    push_neg at hn
    have hh := Finset.sum_nonpos (s:=Finset.univ) (fun j _ => hn j)
    rw [← mean_eval] at hh
    exact (not_le_of_gt hmeanpos) hh
  obtain ⟨j,hj⟩ := hex
  have hjw : 0 < w j := by
    have hne : w j ≠ 0 := by intro he; simpa only [he,zero_mul,lt_self_iff_false] using hj
    exact lt_of_le_of_ne (hw j) hne.symm
  have hjp : 0 < (p j).eval x := by
    by_contra hn
    exact (not_le_of_gt hj) (mul_nonpos_of_nonneg_of_nonpos (hw j) (le_of_not_gt hn))
  have hseg : ∀ t ∈ Icc (0:ℝ) 1, (segment (mean w p) (p j) t).Splits := by
    intro t ht
    rw [← mean_segment_single]
    apply hsplit
    · intro l
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (hw l))
        (by
          split_ifs
          · exact ht.1
          · exact le_rfl)
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_ite_eq',Finset.mem_univ,if_true,hwsum,mul_one]
      ring
  have hselected := segment_roots_le_of_eval_pos hmean.1 (hp j) hmean.2 (hpd j)
    hseg hmeanbelow hmeanpos hjp
  let js : S := ⟨j,by simp [S,hjw]⟩
  have hminj : r i ≤ r js := hmin js (Finset.mem_univ _)
  have hrootj : r js ≤ x := hselected _ (hr js).1
  linarith

end Tusnady.FrameRootSelection
