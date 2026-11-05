import Tusnady.DyadicGeometry

/-!
# Dyadic interval indices and ancestors

An interval of depth `a` is represented by its index in `Fin (2^a)`.
Its points at a common finer dyadic resolution `B` are represented by
`Fin (2^B)`. Membership is precisely the ancestor quotient. Thus the
statements below prove actual nesting, disjointness, and uniqueness of
ancestors in the discrete dyadic geometry, without assuming them.

The embedding of these index intervals as subsets of `ℝ`, and the analytic
Haar/Walsh claims about those subsets, are not proved in this module.
-/

set_option autoImplicit false

namespace Tusnady.Dyadic

/-- The unique interval index at a coarser dyadic depth. -/
def ancestorIndex {b : ℕ} (i : Fin (2 ^ b)) (a : ℕ) (ha : a ≤ b) : Fin (2 ^ a) :=
  ⟨i.val / 2 ^ (b - a), by
    apply (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ (b - a))).2
    have hp : 2 ^ a * 2 ^ (b - a) = (2 : ℕ) ^ b := by
      rw [← pow_add, Nat.add_sub_of_le ha]
    rw [hp]
    exact i.isLt⟩

/-- Successive dyadic ancestor quotients compose. -/
theorem quotient_trans {a b B : ℕ} (ha : a ≤ b) (hb : b ≤ B) (x : ℕ) :
    x / 2 ^ (B - b) / 2 ^ (b - a) = x / 2 ^ (B - a) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]
  congr 2
  omega

/-- Going to depth `b` and then to depth `a` gives the direct ancestor. -/
theorem ancestorIndex_trans {a b B : ℕ} (ha : a ≤ b) (hb : b ≤ B)
    (i : Fin (2 ^ B)) :
    ancestorIndex (ancestorIndex i b hb) a ha = ancestorIndex i a (ha.trans hb) := by
  apply Fin.ext
  exact quotient_trans ha hb i.val

/-- The ancestor at the interval's own depth is the interval itself. -/
theorem ancestorIndex_self {a : ℕ} (i : Fin (2 ^ a)) :
    ancestorIndex i a le_rfl = i := by
  apply Fin.ext
  simp [ancestorIndex]

/-- Euclidean quotient uniqueness is the ancestor uniqueness statement:
exactly one coarse interval can contain a given finer interval. -/
theorem ancestorIndex_unique {a b : ℕ} (ha : a ≤ b) (i : Fin (2 ^ b))
    (j : Fin (2 ^ a))
    (hlo : j.val * 2 ^ (b - a) ≤ i.val)
    (hhi : i.val < (j.val + 1) * 2 ^ (b - a)) :
    ancestorIndex i a ha = j := by
  apply Fin.ext
  exact Nat.div_eq_of_lt_le hlo hhi

/-- A depth-`a` interval as a set of atoms at resolution `B`. -/
def intervalAtoms (B a : ℕ) (i : Fin (2 ^ a)) : Set (Fin (2 ^ B)) :=
  {x | x.val / 2 ^ (B - a) = i.val}

/-- A shared fine atom determines the coarse ancestor of the finer interval. -/
theorem shared_atom_ancestor {a b B : ℕ} (ha : a ≤ b) (hb : b ≤ B)
    (i : Fin (2 ^ a)) (j : Fin (2 ^ b)) (x : Fin (2 ^ B))
    (hx : x ∈ intervalAtoms B a i) (hy : x ∈ intervalAtoms B b j) :
    ancestorIndex j a ha = i := by
  apply Fin.ext
  have hdiv := quotient_trans ha hb x.val
  change x.val / 2 ^ (B - a) = i.val at hx
  change x.val / 2 ^ (B - b) = j.val at hy
  change j.val / 2 ^ (b - a) = i.val
  rw [hy, hx] at hdiv
  exact hdiv

/-- Every interval lies in each of its coarser ancestors. -/
theorem intervalAtoms_subset_ancestor {a b B : ℕ} (ha : a ≤ b) (hb : b ≤ B)
    (j : Fin (2 ^ b)) :
    intervalAtoms B b j ⊆ intervalAtoms B a (ancestorIndex j a ha) := by
  intro x hx
  change x.val / 2 ^ (B - b) = j.val at hx
  change x.val / 2 ^ (B - a) = j.val / 2 ^ (b - a)
  rw [← quotient_trans ha hb x.val, hx]

/-- At a fixed depth, two different interval indices give disjoint intervals. -/
theorem intervalAtoms_disjoint_same_depth {a B : ℕ} (i j : Fin (2 ^ a))
    (hij : i ≠ j) : Disjoint (intervalAtoms B a i) (intervalAtoms B a j) := by
  rw [Set.disjoint_left]
  intro x hx hy
  apply hij
  apply Fin.ext
  exact hx.symm.trans hy

/-- Two dyadic intervals are nested or disjoint. Here both are expressed
on any common refinement; no dyadic nesting axiom is used. -/
theorem intervalAtoms_nested_or_disjoint {a b B : ℕ} (ha : a ≤ B) (hb : b ≤ B)
    (i : Fin (2 ^ a)) (j : Fin (2 ^ b)) :
    intervalAtoms B a i ⊆ intervalAtoms B b j ∨
      intervalAtoms B b j ⊆ intervalAtoms B a i ∨
        Disjoint (intervalAtoms B a i) (intervalAtoms B b j) := by
  classical
  by_cases hex : ∃ x, x ∈ intervalAtoms B a i ∧ x ∈ intervalAtoms B b j
  · obtain ⟨x, hx, hy⟩ := hex
    rcases le_total a b with hab | hba
    · right
      left
      have hancestor := shared_atom_ancestor hab hb i j x hx hy
      simpa only [hancestor] using intervalAtoms_subset_ancestor hab hb j
    · left
      have hancestor := shared_atom_ancestor hba ha j i x hy hx
      simpa only [hancestor] using intervalAtoms_subset_ancestor hba ha i
  · right
    right
    rw [Set.disjoint_left]
    intro x hx hy
    exact hex ⟨x, hx, hy⟩

end Tusnady.Dyadic
