# Mathematical literature

The higher-dimensional lower-bound proof uses the following five intermediate
literature statements. Their formal propositions are in `Tusnady/Literature.lean`;
the unconditional theorem supplies proofs through
`Tusnady.LiteratureProof.assumptionsProved`.

| Result | Formal proof name (prefix `Tusnady.LiteratureProof.`) | Reference |
| --- | --- | --- |
| Gaussian rectangle inequality | `sidak` | Z. Šidák, *Rectangular Confidence Regions for the Means of Multivariate Normal Distributions*, JASA 62 (1967), 626–633. [DOI](https://doi.org/10.1080/01621459.1967.10482935) |
| Gaussian translation inequality, including singular images | `anderson` | T. W. Anderson, *The Integral of a Symmetric Unimodal Function over a Symmetric Convex Set and Some Probability Inequalities*, Proc. AMS 6 (1955), 170–176. [DOI](https://doi.org/10.1090/S0002-9939-1955-0069229-1) |
| Sampling discretization, the `t = 1` case | `sampling` | I. Limonova and V. Temlyakov, *On sampling discretization in L₂*, JMAA 515 (2022), 126457. [DOI](https://doi.org/10.1016/j.jmaa.2022.126457) |
| Differential-entropy chain identity | `conditionalEntropyChainIdentity` | T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed. (2006), Theorem 8.6.2. |
| Joint uniformity of the Rosenblatt transform | `rosenblattUniform` | M. Rosenblatt, *Remarks on a Multivariate Transformation* (1952). [DOI](https://doi.org/10.1214/aoms/1177729394) |

These references identify mathematical origins; they do not act as logical axioms.
The exact formal statements, including their hypotheses and scope, are in the
Lean sources. In particular, the singular Gaussian extension and the sampling
specialization are stated explicitly there.

Nikolov's upper bound and Wei's planar lower bound are outside the current
formalization scope and are not dependencies of its main lower-bound theorem.
For the paper's complete bibliography, see [the manuscript](../paper/Main.pdf).
