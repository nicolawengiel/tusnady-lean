# Verification record

The standalone project passed a complete test from a **fresh GitHub clone** on
5 November 2026, on macOS ARM64. The tested commit was
[`63339a1cffd570d34fbde343b2febac79d94d0c0`](https://github.com/nicolawengiel/tusnady-lean/commit/63339a1cffd570d34fbde343b2febac79d94d0c0).
No existing project installation, dependency checkout, or compiled project
artifact was reused.

## Results

| Check | Result |
| --- | --- |
| Fresh `./scripts/bootstrap.sh` | Exit 0; official Lean 4.24.0 archive checksum matched; nine pinned Git dependencies installed |
| `./scripts/check.sh --complete` | Exit 0; fresh build completed successfully (3,576 Lake jobs) |
| Exact unconditional main declaration type | `Tusnady.HigherDimensionalLowerBound`, with no additional literature parameter |
| Main theorem and expanded real-coloring witness | Both checked; only standard Lean axioms |
| Exhaustive imported project-theorem audit | 3,275 declarations; only standard Lean axioms |
| Separately built, non-imported OpenMapping helper module | Four further theorems audited; only standard Lean axioms |
| `LiteratureAudit.lean` | All five exact literature declaration types checked; only standard Lean axioms |
| `./scripts/bootstrap.sh --offline` | Exit 0; installed revisions and full required mathlib import chain checked |
| Tracked checkout files after the checks | Unchanged |

The only observed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The component, main, and literature counts describe separate checks and overlap;
they should not be added as a count of distinct theorems.

The toolchain and dependencies were installed anew. Bootstrap fetched 3,333
upstream mathlib cache files; it did not rebuild all of mathlib from source.
All 234 project library source modules were built, including the one helper
module not imported by the main library. The repository's proof sources,
verification scripts, and version pins are byte-identical to those tested.
Subsequent changes concern publication documentation and archive metadata only.

## Evidence

[Machine-readable record and exact code hashes](verification-fresh.json)
include command exit codes, timestamps, version pins, and log hashes.
Selected original outputs are included:

- [Main declaration types and axioms](verification/fresh-main.log).
- [Full imported-component audit (gzip)](verification/fresh-components.log.gz).
- [Non-imported helper module](verification/fresh-unused.log).
- [Five literature statements](verification/fresh-literature.log).
- [Offline installation check](verification/fresh-offline.log).

The complete build/check log, retained with the local test artifacts, has SHA-256
`753504ea678ebe29b2ab86e9b00cf179f72d062e5e6a9b8f094ed451406e7d0c`.
The earlier working-copy audit is recorded separately in
[verification-source.json](verification-source.json); it is not used as a
substitute for this fresh test.

## Reproduce

Follow [BUILD.md](BUILD.md). In addition to the standard complete check, the
otherwise non-imported helper can be built with:

```sh
./scripts/lake.sh build Tusnady.External.RealRooted.Mathlib.Analysis.Complex.OpenMapping
./scripts/lake.sh env lean LiteratureAudit.lean
```

The exhaustive per-theorem axiom audit takes substantially longer than the build
and emits its collected output when it finishes. This fresh full build and audit
took about 25 minutes on the tested installation, excluding initial downloads.

This records a macOS ARM64 test, not tests on other operating systems. The
formalized scope is the higher-dimensional lower bound described in
[SCOPE.md](SCOPE.md); the matching upper bound, planar case, and manuscript
extensions are outside this version's scope.
