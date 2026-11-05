# Verification record

This record describes checks observed on 5 November 2026. It is a preparation
record, not a release announcement. The exhaustive unconditional audit completed
in the original pinned macOS ARM64 installation. A fresh full rebuild of this
standalone publication copy has **not** been performed.

## Completed source audit

The source project ran its complete check with Lean 4.24.0 and mathlib revision
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. The associated offline bootstrap
check reported nine unchanged pinned Git dependencies. The Lean executable
reported `arm64-apple-darwin23.6.0`, commit
`797c613eb9b6d4ec95db23e3e00af9ac6657f24b`.

The completed log contains:

| Evidence | Result |
| --- | --- |
| Exhaustive project declaration audit, line 14624 | 3,275 declarations; only standard Lean axioms |
| `Tusnady.main_lower_bound_unconditional`, lines 14625–14627 | Exact type `Tusnady.HigherDimensionalLowerBound`; only standard Lean axioms |
| `Tusnady.main_lower_bound_real_colorings_unconditional`, lines 14628–14643 | Expanded unconditional witness statement; only standard Lean axioms |
| Final declaration audit, line 14647 | Both unconditional declarations passed |
| Final success marker, line 14648 | Complete unconditional target checked successfully |

The observed recursive axiom dependencies are `propext`, `Classical.choice`,
and `Quot.sound`. A separate type-guard check rejected the conditional
declaration and accepted the unconditional declaration. A separate check of four
unused ported theorems also reported only standard axioms.

The original complete log, `verification-unconditional-run.log`, has 14,648 lines
and 1,181,044 bytes. Its SHA-256 is:

```text
5b18d5e6cadaf06e39bf57d1250245b2f5f9bf8f1232967275ab67e28842a1e0
```

Its last modification time was `2026-11-05T12:03:58.846852+00:00`; this is a
filesystem evidence timestamp, not a release timestamp. Full original logs are
not bundled in this publication copy. Their hashes and the selected observations
are recorded in [verification-source.json](verification-source.json). A log hash
identifies the retained evidence; it does not replace rerunning the checks.

## Source identity and packaging checks

All 237 Lean source files and all three build/version configuration files
(`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`) match the source
snapshot byte for byte. Their exact SHA-256 values in
[verification-source.json](verification-source.json) were copied from the
preparation manifest frozen at `2026-11-05T11:58:44.521081+00:00` and checked
against both the original source and this copy after the audit completed.
All 251 files recorded in that manifest still match the original source.

The standalone copy differs from those recorded files only in two documented
packaging edits: `.gitignore` adds `.DS_Store`, `__pycache__/`, and `*.pyc`;
`scripts/check.sh` removes the development-only manuscript-preservation
invocation. No Lean audit or theorem-type check was removed. New publication
documentation and citation metadata are outside that original file manifest.

The following standalone checks passed without building Lean:

- `python3 scripts/audit_cache_roots.py`: 237 Lean files passed the source scan;
  all 151 direct mathlib imports are covered by the 153 configured cache roots.
  This invocation checks import coverage, not installed dependency artifacts.
- SHA-256 comparison of every copied manifest file, allowing only the two
  packaging edits above.
- `sh -n` for every shell script and executable permission checks for those
  scripts; Python `compile()` syntax checks for every Python script.
- Relative Markdown link checks and absence of bundled `.lake/`, `.toolchains/`,
  `.downloads/`, and `.cache/` directories.

These are source and packaging checks. Shell/Python syntax checks do not prove
the scripts' behavior, and the checks do not establish a fresh standalone build.

## Remaining work and scope

A fresh full standalone bootstrap, build, final declaration-type check, and
recursive axiom audit remain to be run using the [build instructions](BUILD.md).
No successful fresh installation or other-platform run is claimed here.
The original software is licensed under Apache-2.0; the manuscript PDF is
explicitly excluded. Confirmation of the intended public manuscript version
remains pending.

The mathematical scope remains the higher-dimensional lower bound described in
[SCOPE.md](SCOPE.md). This record does not claim the planar lower bound, matching
upper bound, or the manuscript's algorithmic and polytope extensions.
