/- Proven compatibility helpers for the pre-4.35 polynomial splitting API.
The project keeps its pinned Lean/mathlib 4.24 versions. -/
import Mathlib.Algebra.Polynomial.Splits

namespace Polynomial
variable {K : Type*} [Field K] {p : K[X]}

theorem Splits.eq_prod_roots (hp : p.Splits (RingHom.id K)) :
    p = C p.leadingCoeff * (p.roots.map fun a => X - C a).prod :=
  eq_prod_roots_of_splits_id hp

theorem Splits.eval_eq_prod_roots (hp : p.Splits (RingHom.id K)) (x : K) :
    p.eval x = p.leadingCoeff * (p.roots.map fun a => x - a).prod :=
  eval_eq_prod_roots_sub_of_splits_id hp x

theorem Splits.natDegree_eq_card_roots (hp : p.Splits (RingHom.id K)) :
    p.natDegree = p.roots.card :=
  (splits_iff_card_roots.mp hp).symm

theorem Splits.eval_derivative_div_eval_of_ne_zero (hp : p.Splits (RingHom.id K))
    {x : K} (hx : p.eval x ≠ 0) :
    p.derivative.eval x / p.eval x = (p.roots.map fun r => 1 / (x - r)).sum :=
  eval_derivative_div_eval_of_ne_zero_of_splits hp hx

theorem Splits.roots_ne_zero (hp : p.Splits (RingHom.id K)) (hd : p.natDegree ≠ 0) :
    p.roots ≠ 0 := by
  intro hzero
  have hcard := splits_iff_card_roots.mp hp
  rw [hzero, Multiset.card_zero] at hcard
  exact hd hcard.symm

end Polynomial
