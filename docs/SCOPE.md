# Formalization scope

The main target is the manuscript's higher-dimensional lower bound (Theorem 1.1).
For each natural dimension `d ≥ 3`, there exist a real constant `c > 0` and a
natural threshold `N₀ ≥ 1` such that for every `N ≥ N₀` there is an injective
point family `P : Fin N → Point d`, whose image has cardinality exactly `N`,
with the following property: for every real-valued sign coloring of these points,
there is a closed lower orthant with absolute signed count at least
`c * Real.rpow (Real.log (N : ℝ)) ((d : ℝ) - (1 / 2 : ℝ))`.

The constants precede `N`; the points precede the coloring; the orthant may depend
on the coloring. `Real.log` is the natural logarithm and `Real.rpow` the real power.
No balanced-coloring restriction is imposed.

The exact statement appears in
[`MainUnconditional.lean`](../Tusnady/MainUnconditional.lean); underlying
geometric and discrepancy definitions appear in
[`Definitions.lean`](../Tusnady/Definitions.lean).

The five intermediate literature propositions are discharged by
`Tusnady.LiteratureProof.assumptionsProved` in the unconditional target.
The older conditional theorem remains as part of the proof organization.

## Possible subsequent extensions

A future formalization of Nikolov's upper bound can be added within the same
repository, with clear attribution and an explicit theorem about the same
point sets, coloring convention, and box family. Combining formal upper and lower
bounds would yield the matching order for dimensions `d ≥ 3`.

To claim the complete result for all fixed `d ≥ 2`, the planar lower bound must
also be included or imported from a compatible, checked formalization of Wei's
result. A bibliographic reference alone does not provide a Lean proof term.
Compatibility of definitions, theorem statements, dependencies, and licensing
would need to be checked before importing external Lean code.

The algorithmic and polytope extensions in the manuscript are outside the scope
of this initial version. Future additions should be recorded as subsequent
releases, preserving the initial lower-bound snapshot.
