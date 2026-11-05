import Tusnady.External.RealRooted.Mathlib.Analysis.Complex.Polynomial.ClosedRoots
import Tusnady.External.RealRooted.RealPolynomialStability
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecificLimits.Basic

/-! Root control along real-rooted monic segments. The only ported analytic
input is the proved closed-root-set limit theorem of RealRooted (Apache-2.0,
revision 5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837). No common interlacer is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Tusnady.FrameRootSelection
open Polynomial Set Filter
open scoped BigOperators Topology NNReal

/-- The genuine coefficientwise affine polynomial segment. -/
def segment (p q : ℝ[X]) (t : ℝ) : ℝ[X] := (1-t) • p+t • q

@[simp] lemma segment_zero (p q : ℝ[X]) : segment p q 0 = p := by simp [segment]
@[simp] lemma segment_one (p q : ℝ[X]) : segment p q 1 = q := by simp [segment]
@[simp] lemma segment_coeff (p q : ℝ[X]) (t : ℝ) (j : ℕ) :
    (segment p q t).coeff j = (1-t)*p.coeff j+t*q.coeff j := by simp [segment]
@[simp] lemma segment_eval (p q : ℝ[X]) (t x : ℝ) :
    (segment p q t).eval x = (1-t)*p.eval x+t*q.eval x := by simp [segment]

lemma segment_natDegree_le {p q : ℝ[X]} {d : ℕ} (hp : p.natDegree ≤ d)
    (hq : q.natDegree ≤ d) (t : ℝ) : (segment p q t).natDegree ≤ d := by
  exact (natDegree_add_le _ _).trans (max_le
    ((natDegree_smul_le _ _).trans hp) ((natDegree_smul_le _ _).trans hq))

lemma segment_monic_degree {p q : ℝ[X]} {d : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) (t : ℝ) :
    (segment p q t).Monic ∧ (segment p q t).natDegree = d := by
  have hle := segment_natDegree_le hpd.le hqd.le t
  have hpc : p.coeff d = 1 := hpd ▸ hp.coeff_natDegree
  have hqc : q.coeff d = 1 := hqd ▸ hq.coeff_natDegree
  have hc : (segment p q t).coeff d = 1 := by
    rw [segment_coeff,hpc,hqc]
    ring
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one d hle hc,
    le_antisymm hle (le_natDegree_of_ne_zero (by rw [hc]; norm_num))⟩

/-- An explicit common Cauchy bound for every polynomial in a compact
monic equal-degree segment. -/
def segmentBound (p q : ℝ[X]) (d : ℕ) : ℝ≥0 :=
  (Finset.range d).sup (fun j => max ‖p.coeff j‖₊ ‖q.coeff j‖₊)+1

lemma segment_root_bound {p q : ℝ[X]} {d : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = d) (hqd : q.natDegree = d) {t r : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hr : (segment p q t).IsRoot r) :
    |r| ≤ (segmentBound p q d : ℝ) := by
  have hm := segment_monic_degree hp hq hpd hqd t
  have hc (j : ℕ) : ‖(segment p q t).coeff j‖₊ ≤ max ‖p.coeff j‖₊ ‖q.coeff j‖₊ := by
    apply NNReal.coe_le_coe.mp
    change ‖(segment p q t).coeff j‖ ≤ max ‖p.coeff j‖ ‖q.coeff j‖
    rw [segment_coeff]
    calc
      _ ≤ ‖(1-t)*p.coeff j‖+‖t*q.coeff j‖ := norm_add_le _ _
      _ = (1-t)*‖p.coeff j‖+t*‖q.coeff j‖ := by
        rw [norm_mul,norm_mul,Real.norm_of_nonneg (by linarith [ht.2]),Real.norm_of_nonneg ht.1]
      _ ≤ _ := by
        have ha := max_le_iff.mp (le_refl (max ‖p.coeff j‖ ‖q.coeff j‖))
        nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr ha.1),
          mul_nonneg ht.1 (sub_nonneg.mpr ha.2)]
  have hb : (segment p q t).cauchyBound ≤ segmentBound p q d := by
    simp only [Polynomial.cauchyBound,hm.2,hm.1.leadingCoeff,nnnorm_one,div_one,segmentBound]
    exact add_le_add_right (Finset.sup_le fun j hj =>
      (hc j).trans (Finset.le_sup (f:=fun j => max ‖p.coeff j‖₊ ‖q.coeff j‖₊) hj)) 1
  have hrb := (hr.norm_lt_cauchyBound hm.1.ne_zero).le.trans hb
  exact_mod_cast hrb

end Tusnady.FrameRootSelection

namespace Tusnady.FrameRootSelection
open Polynomial Set Filter
open scoped BigOperators Topology NNReal

/-- Positive evaluation at a fixed threshold prevents roots from passing
that threshold along any real-splitting monic segment. This proves the
selection mechanism directly; it does not assume a common interlacer. -/
theorem segment_roots_le_of_eval_pos {p q : ℝ[X]} {d : ℕ} {x : ℝ}
    (hp : p.Monic) (hq : q.Monic) (hpd : p.natDegree = d) (hqd : q.natDegree = d)
    (hsplit : ∀ t ∈ Icc (0:ℝ) 1, (segment p q t).Splits (RingHom.id ℝ))
    (hpbelow : ∀ r ∈ p.roots, r < x)
    (hpx : 0 < p.eval x) (hqx : 0 < q.eval x) : ∀ r ∈ q.roots, r ≤ x := by
  intro r hr
  by_contra hrx
  have hxr : x < r := lt_of_not_ge hrx
  let B : ℝ := segmentBound p q d
  let G : Set (ℝ × ℝ) := (Icc (0:ℝ) 1 ×ˢ Icc (-B) B) ∩
    {z | x ≤ z.2 ∧ (segment p q z.1).eval z.2 = 0}
  have heval : Continuous (fun z : ℝ × ℝ => (segment p q z.1).eval z.2) := by
    simp only [segment_eval]
    fun_prop
  have hGc : IsCompact G := (isCompact_Icc.prod isCompact_Icc).inter_right
    ((isClosed_le continuous_const continuous_snd).inter (isClosed_eq heval continuous_const))
  have hGne : G.Nonempty := by
    have hrroot : q.IsRoot r := Polynomial.isRoot_of_mem_roots hr
    have hrb : |r| ≤ B := by
      simpa only [segment_one] using
        segment_root_bound hp hq hpd hqd (t:=1) ⟨by norm_num,le_rfl⟩ (by simpa using hrroot)
    exact ⟨(1,r),⟨⟨by norm_num,⟨(abs_le.mp hrb).1,(abs_le.mp hrb).2⟩⟩,
      hxr.le,by simpa using hrroot⟩⟩
  obtain ⟨z,hz,hmin⟩ := hGc.exists_isMinOn hGne continuous_fst.continuousOn
  have ht : z.1 ∈ Icc (0:ℝ) 1 := hz.1.1
  have hzroot : (segment p q z.1).IsRoot z.2 := hz.2.2
  have htz : 0 < z.1 := by
    by_contra hn
    have he : z.1 = 0 := le_antisymm (le_of_not_gt hn) ht.1
    have hpr : z.2 ∈ p.roots := by
      apply (Polynomial.mem_roots hp.ne_zero).2
      simpa only [he,segment_zero] using hzroot
    exact (not_lt_of_ge hz.2.1) (hpbelow z.2 hpr)
  have hxne : (segment p q z.1).eval x ≠ 0 := by
    rw [segment_eval]
    exact ne_of_gt (by nlinarith [mul_pos htz hqx,mul_nonneg (sub_nonneg.mpr ht.2) hpx.le])
  have hzx : x < z.2 := lt_of_le_of_ne hz.2.1 (by
    intro he
    exact hxne (by simpa only [he] using hzroot))
  let u : ℕ → ℝ := fun n => z.1*(1-1/((n:ℝ)+1))
  have hun (n : ℕ) : 0 ≤ u n := by
    dsimp only [u]
    apply mul_nonneg htz.le
    have hden : 0 < (n:ℝ)+1 := by positivity
    have hn : (0:ℝ) ≤ n := by positivity
    have hfrac : 1/((n:ℝ)+1) ≤ 1 := (div_le_one hden).2 (by linarith)
    linarith
  have hult (n : ℕ) : u n < z.1 := by
    dsimp only [u]
    have hfrac : 0 < 1/((n:ℝ)+1) := by positivity
    nlinarith
  have humem (n : ℕ) : u n ∈ Icc (0:ℝ) 1 := ⟨hun n,(hult n).le.trans ht.2⟩
  have hulim : Tendsto u atTop (𝓝 z.1) := by
    have hl : Tendsto (fun n : ℕ => z.1*((1:ℝ)-1/((n:ℝ)+1))) atTop (𝓝 (z.1*(1-0))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa only [sub_zero,mul_one] using hl
  have hbelow (n : ℕ) (s : ℝ) (hs : s ∈ (segment p q (u n)).roots) : s < x := by
    by_contra hn
    have hsroot := Polynomial.isRoot_of_mem_roots hs
    have hsb := segment_root_bound hp hq hpd hqd (humem n) hsroot
    have hG : (u n,s) ∈ G :=
      ⟨⟨humem n,⟨(abs_le.mp hsb).1,(abs_le.mp hsb).2⟩⟩,le_of_not_gt hn,hsroot⟩
    have hmin' : z.1 ≤ u n := hmin hG
    exact (not_le_of_gt (hult n)) hmin'
  have hclosed : IsClosed {w : ℂ | w.re ≤ x} := isClosed_le Complex.continuous_re continuous_const
  have hlimit := Polynomial.roots_mem_of_tendsto_eval_of_natDegree_le
    hclosed (p:=fun n => (segment p q (u n)).map Complex.ofRealHom)
    (p₀:=(segment p q z.1).map Complex.ofRealHom) (N:=d)
    (fun n => by
      rw [Polynomial.natDegree_map_eq_of_injective Complex.ofRealHom.injective]
      exact segment_natDegree_le hpd.le hqd.le (u n))
    (fun n w hw => by
      rw [Polynomial.roots_map Complex.ofRealHom (hsplit _ (humem n))] at hw
      obtain ⟨s,hs,rfl⟩ := Multiset.mem_map.mp hw
      exact (hbelow n s hs).le)
    (by
      intro w
      have hev (t : ℝ) : ((segment p q t).map Complex.ofRealHom).eval w =
          (1-(t:ℂ))*(p.map Complex.ofRealHom).eval w+(t:ℂ)*(q.map Complex.ofRealHom).eval w := by
        simp [segment,Polynomial.smul_eq_C_mul]
      simp only [hev]
      exact ((tendsto_const_nhds.sub (Complex.continuous_ofReal.tendsto z.1 |>.comp hulim)).mul tendsto_const_nhds).add
        ((Complex.continuous_ofReal.tendsto z.1 |>.comp hulim).mul tendsto_const_nhds))
  have hrootcomplex : (z.2:ℂ) ∈ ((segment p q z.1).map Complex.ofRealHom).roots := by
    rw [Polynomial.roots_map Complex.ofRealHom (hsplit _ ht)]
    exact Multiset.mem_map.mpr ⟨z.2,(Polynomial.mem_roots
      (segment_monic_degree hp hq hpd hqd z.1).1.ne_zero).2 hzroot,rfl⟩
  exact (not_le_of_gt hzx) (hlimit _ hrootcomplex)

end Tusnady.FrameRootSelection
