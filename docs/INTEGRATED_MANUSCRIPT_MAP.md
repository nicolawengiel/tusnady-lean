# The mathematical statements in Lean

The joint theorem is
`Tusnady.Integrated.main_sharp_order : Tusnady.Integrated.CombinedSharpOrder`.
For every integer `d ≥ 2` there are `c > 0`, `C > 0` and an integer `N₀ ≥ 2`
such that for **every** `N ≥ N₀`,

```text
c (log N)^(d − 1/2)
  ≤ worstDiscrepancy(orthants, d, N)
  ≤ worstDiscrepancy(boxes, d, N)
  ≤ C (log N)^(d − 1/2).
```

Here `log` is the natural logarithm. The [definition of the target](../Tusnady/Integrated/Statements.lean)
uses positive constants and a threshold chosen before `N`. The [proof](../Tusnady/Integrated/Main.lean)
also gives separate Θ statements and explicit upper and lower statements for
real sign colorings of closed boxes.

| Manuscript statement or proof step | Formal declaration or source |
| --- | --- |
| Worst-case combinatorial discrepancy for closed lower orthants in real space. A configuration represents exactly `N` distinct points and all real ±1 colorings are allowed. | [Definitions](../Tusnady/Definitions.lean). A configuration is an injective function `P : Fin N → Point d`. The definitions `Tusnady.Anchored`, `Tusnady.IsSignColoring` and `Tusnady.worstDiscrepancy` specify queries, signs and the extremum. |
| Wengiel, [Theorem 1.1](https://arxiv.org/html/2611.06998v1#S1), the lower bound for fixed `d ≥ 3`. | [`Tusnady.main_lower_bound_unconditional`](../Tusnady/MainUnconditional.lean) and `Tusnady.main_lower_bound_real_colorings_unconditional`. |
| Inputs used in that proof: the Šidák and Anderson Gaussian inequalities, sampling discretization, the conditional entropy identity and uniformity of Rosenblatt coordinates. | The [literature audit](../LiteratureAudit.lean) lists the project proofs `Tusnady.LiteratureProof.sidak`, `anderson`, `sampling`, `conditionalEntropyChainIdentity` and `rosenblattUniform`. |
| Wei's [planar lower bound](https://arxiv.org/abs/2610.08130) and its deterministic consequence. | [`R56Audit.exists_points`](../Wei/R56Audit/Parameters.lean) supplies distinct planar points. The [coordinate and coloring conversion](../Tusnady/PlanarWei/Coordinates.lean) and [natural-log conversion](../Tusnady/PlanarWei/LowerBound.lean) prove `Tusnady.PlanarWei.planar_lower_bound`. [Wei source details](WEI_SOURCE_REVIEW.md). |
| Nikolov's [Theorem 1 and §4](https://doi.org/10.1112/S0025579317000250), the upper bound in every fixed dimension `d ≥ 2`. | [`Tusnady.main_upper_bound`](../Tusnady/Upper/Main.lean), `Tusnady.main_upper_bound_real_colorings` and `Tusnady.main_upper_bound_asymptotic`. A single coloring controls every orthant. The finite statement uses `log(2 + N)`; its asymptotic version uses `log N`. [Upper-bound sources](UPPER_LITERATURE_AND_PROVENANCE.md). |
| Comparison between closed lower orthants and bounded closed boxes with finite, real corners. | [Thresholds](../Tusnady/Boxes/Thresholds.lean), [indicator expansion](../Tusnady/Boxes/ProductExpansion.lean) and [orthant comparison](../Tusnady/Boxes/OrthantComparison.lean) prove the same-coloring inequalities with factor `2^d`. The [corner formulation](../Tusnady/Boxes/Corners.lean) includes degenerate and empty boxes. |
| Sharp order for every fixed `d ≥ 2`. | [`Tusnady.Integrated.lower_bound`](../Tusnady/Integrated/Lower.lean) combines the two lower bounds. The [combined theorem](../Tusnady/Integrated/Main.lean) and its `orthant_isTheta`, `boxes_isTheta`, `boxes_upper_bound_real_colorings` and `boxes_lower_bound_real_colorings` forms follow. |

[IntegratedAudit.lean](../IntegratedAudit.lean) compares the actual theorem
types with independently written formulas and follows their axiom dependencies.
The joint theorem uses only `propext`, `Classical.choice` and `Quot.sound`.
The polytopes and algorithmic consequences in §8 of Wengiel's paper are
outside the scope of this release.
