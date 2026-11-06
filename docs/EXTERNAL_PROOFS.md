# Reused Lean proofs

The sampling argument in the higher-dimensional lower bound uses
polynomial stability and a Marcus–Spielman–Srivastava bound on mixed
characteristic polynomials. Several underlying modules are adapted from
[Per Alexandersson et al., *RealRooted*, revision
`5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837`](https://github.com/PerAlexandersson/RealRooted/tree/5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837).
The [adapted files](../Tusnady/External/RealRooted/) retain their source paths,
revision and [Apache-2.0 license](../Tusnady/External/RealRooted/LICENSE).
They cover multivariate polynomial stability, determinantal stability
and the estimates used in
[`MSSBound.lean`](../Tusnady/External/RealRooted/MultivariateStability/MSSBound.lean).

The project's [finite-frame lemmas](../Tusnady/FrameMSS.lean) and
[frame selection argument](../Tusnady/FrameMSSSelection.lean) apply
the polynomial bounds in the proof of sampling discretization. Source headers
record the original attribution through the adaptations across Lean versions.

The other incorporated proofs are [Wei's planar lower-bound
formalization](WEI_SOURCE_REVIEW.md), licensed under MIT, and the [Gaussian
analysis modules from OpenAI/math](UPPER_LITERATURE_AND_PROVENANCE.md),
licensed under Apache-2.0. [NOTICE](../NOTICE) records the software credits
and licenses.
