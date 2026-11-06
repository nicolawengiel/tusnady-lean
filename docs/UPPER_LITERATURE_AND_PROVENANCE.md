# Nikolov's upper bound and its formal proof

The [upper-bound module](../Tusnady/Upper/Main.lean) formalizes Theorem 1
of Aleksandar Nikolov, [*Tighter bounds for the discrepancy of boxes and
polytopes*](https://doi.org/10.1112/S0025579317000250), *Mathematika* 63
(2017), 1091–1113. For every configuration in fixed dimension `d ≥ 2`, one
sign coloring controls the counts in all closed lower orthants. The finite
bound uses `(log(2 + N))^(d − 1/2)`; the asymptotic bound uses `log N`.

The geometric argument follows Nikolov's §4. A
[dyadic factorization](../Tusnady/Upper/DyadicFactorization.lean) represents
the incidences in the first `d − 1` coordinates, including tied coordinates.
Sorting the final coordinate turns the remaining query into a prefix.
[Prefix signing](../Tusnady/Upper/PrefixBalancing.lean) controls all prefixes
using one choice of signs. A [finite Gaussian estimate](../Tusnady/Upper/GaussianBody.lean)
supplies a convex body of sufficient Gaussian mass.

Nikolov invokes a signed-series theorem of Wojciech Banaszczyk,
[*On series of signed vectors and their rearrangements*](https://doi.org/10.1002/rsa.20373).
The formalization proves a variant with universal factor 1000. The analytic
argument follows Maud Szusterman's
[*Monotonicity of the Gaussian measure under Banaszczyk transforms*](https://arxiv.org/abs/2510.00842v2)
and uses the Gaussian symmetrization framework of Antoine Ehrhard,
[*Symétrisation dans l'espace de Gauss*](https://doi.org/10.7146/math.scand.a-12035).
The formal [Gaussian fold estimate](../Tusnady/Upper/Ehrhard/VerticalFoldMonotonicity.lean)
at radius `1/1000` supplies the [prefix theorem](../Tusnady/Upper/PrefixSmallRadius.lean).
The larger absolute constant preserves Nikolov's discrepancy exponent and
the required dependence of the upper constant on the dimension alone.

Eight Lean modules in the Gaussian analysis adapt software from
[OpenAI/math, revision `4eaee87548250b2682affda7d05d947c05554bae`](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae):
`Quantile`, `QuantileCalculus`, `HeatMaximum`, `Translation`, `Stein`,
`HeatConvolution`, `SmoothedConcavity` and `SoftMinimum`. They supply parts
of the smooth quantile and heat-equation argument. The project extends
the soft-minimum calculation to affine scores and derives the convex
approximation, isoperimetry and fold estimates that it uses. The
[provenance manifest](../vendor/openai-math-4eaee875/provenance.json) lists
the source paths and revisions. The 14 source files in the original import
closure are preserved for comparison, together with their
[Apache-2.0 license](../vendor/openai-math-4eaee875/LICENSE).
