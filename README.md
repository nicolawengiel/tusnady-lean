# Tusnády's problem in Lean 4

Lean 4 formalization accompanying Nicola Wengiel's *Resolving Tusnády's Problem*.

## Scope

This version concerns the **higher-dimensional lower bound only**: for every fixed
`d ≥ 3`, and every sufficiently large `N`, there are exactly `N` distinct points
whose combinatorial discrepancy for closed lower orthants is at least
`c_d (log N)^(d − 1/2)`, with `c_d > 0` independent of `N`.

It does not include Nikolov's matching upper bound, Wei's planar lower bound,
or the manuscript's algorithmic and polytope extensions. It is therefore not
presented as a formalization of the complete resolution in all dimensions.

The target declaration is:

```lean
Tusnady.main_lower_bound_unconditional : Tusnady.HigherDimensionalLowerBound
```

The fully expanded statement is
`Tusnady.main_lower_bound_real_colorings_unconditional`; both are in
[Tusnady/MainUnconditional.lean](Tusnady/MainUnconditional.lean).
See [scope and quantifiers](docs/SCOPE.md).

## Verify

From the repository root:

```sh
./scripts/bootstrap.sh
./scripts/check.sh --complete
```

The project pins Lean 4.24.0 and mathlib to exact revisions. See
[build instructions](docs/BUILD.md) for requirements and verification details.

**Verification status:** this is a preparation snapshot. The exhaustive audit
completed successfully in the original pinned macOS ARM64 environment: 3,275
project declarations and both unconditional declarations passed their axiom
checks. This copy has byte-identical Lean sources and build/version configuration.
Standalone source, import-coverage, and packaging checks passed. A fresh full
standalone rebuild has **not** been performed. See the
[verification record and source hashes](docs/VERIFICATION.md) for the evidence
and its limits.

## Paper and sources

- [Manuscript snapshot](paper/Main.pdf) and [snapshot information](paper/README.md).
- [Mathematical literature](docs/LITERATURE.md).
- [Attribution for reused formal proofs](docs/EXTERNAL_PROOFS.md).

Repository: <https://github.com/nicolawengiel/tusnady-lean>.
An arXiv link and version-specific archival DOI will be added when available.

## Licensing

Original project code, scripts, configuration, and software documentation are
licensed under [Apache-2.0](LICENSE). Reused RealRooted files retain their original
Apache-2.0 license and attribution notices; see [NOTICE](NOTICE).
The manuscript PDF is excluded from this software license; see
[the manuscript copyright notice](paper/README.md).
