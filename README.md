# Tusnády's problem in Lean 4

This project gives a machine-checked proof of the sharp order of the worst-case
combinatorial discrepancy of axis-parallel boxes. It accompanies Nicola Wengiel's
paper [*Resolving Tusnády's Problem* (arXiv:2611.06998v1)](https://arxiv.org/abs/2611.06998v1).

For each fixed dimension `d ≥ 2`, both closed lower orthants and bounded closed
axis-parallel boxes have worst-case discrepancy of order `(log N)^(d − 1/2)`.
The positive lower and upper constants and the threshold for `N` depend only
on `d`. For the lower bound, there is a set of exactly `N` distinct points
on which every sign coloring has large discrepancy. For the upper bound, every
set of `N` distinct points admits a single coloring that controls all boxes.

```lean
import Tusnady.Integrated

#check Tusnady.Integrated.main_sharp_order
#check Tusnady.Integrated.orthant_isTheta
#check Tusnady.Integrated.boxes_isTheta
#print axioms Tusnady.Integrated.main_sharp_order
```

The formalization combines Wengiel's lower bound for `d ≥ 3`, Zhewei Wei's
planar lower bound and Aleksandar Nikolov's matching upper bound. The
[manuscript-to-Lean reference](docs/INTEGRATED_MANUSCRIPT_MAP.md) identifies
each result and its Lean declaration. The paper also treats polytopes and
algorithmic consequences, which are outside the scope of this software.

## Reproduce the verification

Clone this release and run the two scripts from the repository root:

```sh
git clone --branch v0.2.0 --depth 1 https://github.com/nicolawengiel/tusnady-lean.git
cd tusnady-lean
./scripts/bootstrap.sh
./scripts/check-integrated.sh --standalone
```

The same two scripts work from an extracted release archive. The bootstrap
installs the pinned Lean 4.34.1 toolchain locally and retrieves the dependencies
in `lake-manifest.json`, including mathlib at
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The final script builds the proof,
checks the main theorem types against separately stated formulas and audits
their dependencies. The joint theorem uses only `propext`, `Classical.choice`
and `Quot.sound`.

An independent rebuild from the source archive at revision
`2896887242bab9f66071cce72127474b1ad42937` compiled all 406 project modules
outside the audit files with a fresh project cache. The 15 main theorem type
checks and the full standalone audit passed. See the [verification report,
logs and attestations](docs/release-v0.2.0/).

## Sources and licenses

- The planar proof reuses [Zhewei Wei's Lean formalization](https://github.com/wzskytop/tusnady-lean/tree/6f14d177668e79a9155f7cd60496313514ad0c9e)
  for [*Tight Bounds for Tusnády's Problem in the Plane*](https://arxiv.org/abs/2610.08130).
  The integrated modules preserve Wei's proof bodies and MIT notices. Their
  local import paths and attribution headers were adapted. Separate lemmas
  translate Wei's result into the point, coloring and discrepancy definitions
  used here. See the [record of the integration](docs/WEI_SOURCE_REVIEW.md).
- The upper bound follows Aleksandar Nikolov's
  [*Tighter Bounds for the Discrepancy of Boxes and Polytopes*](https://doi.org/10.1112/S0025579317000250).
  The formal proof uses a larger absolute constant at the prefix-balancing step,
  which preserves the stated asymptotic order. The
  [upper-bound source notes](docs/UPPER_LITERATURE_AND_PROVENANCE.md) describe
  the analytic lemmas adapted from [OpenAI/math](https://github.com/openai/math/tree/4eaee87548250b2682affda7d05d947c05554bae).
- The lower-bound formalization includes selected proofs from
  [Per Alexandersson et al., RealRooted](https://github.com/PerAlexandersson/RealRooted/tree/5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837).
  The [external proof notes](docs/EXTERNAL_PROOFS.md) identify those sources.

Original project code and software documentation are licensed under
[Apache-2.0](LICENSE). The reused OpenAI/math and RealRooted files retain
their Apache-2.0 notices. Wei's software retains its MIT license. See
[NOTICE](NOTICE) for attributions and the [paper snapshot](paper/README.md)
for the separate manuscript copyright terms.

## Citation

Please cite the [archived v0.2.0 release (DOI: 10.5281/zenodo.24000482)](https://doi.org/10.5281/zenodo.24000482)
and the [accompanying paper](https://arxiv.org/abs/2611.06998v1).
The [previous release, v0.1.0](https://doi.org/10.5281/zenodo.23980543),
archived the higher-dimensional lower bound alone.
