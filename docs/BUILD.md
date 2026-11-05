# Build and verification

Run all commands from the repository root. The pinned toolchain is Lean 4.24.0;
mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
Keep `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` together.
The lockfile records nine Git dependencies.

## First installation

Requirements: internet access, Git, Python 3, `curl`, and `tar` with Zstandard
support (which may require a separate `zstd` executable).

```sh
./scripts/bootstrap.sh
./scripts/check.sh --complete
```

Bootstrap installs a local toolchain into `.toolchains/`, dependency sources
and build artifacts into `.lake/`, and downloads/caches into `.downloads/`
and `.cache/`. No global Lean installation is needed.

Bootstrap recognizes macOS ARM64/x86_64 and Linux ARM64/x86_64. The existing
source environment is macOS ARM64; fresh installation and the other platforms
have not yet been tested for this publication copy. Only the macOS ARM64
archive has a bundled checksum, derived from the original downloaded archive.

## Subsequent local checks

After bootstrap has completed, installed dependencies and their imports can be
checked offline with:

```sh
./scripts/bootstrap.sh --offline
./scripts/check.sh --complete
```

The complete check validates dependency revisions, source/import coverage,
and absence of forbidden proof placeholders; builds the library; checks the
actual main declaration type; and audits recursive axiom dependencies.
The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Logs are written under `.cache/audit-logs/`.

The declaration type must be exactly `Tusnady.HigherDimensionalLowerBound`.
The check does not accept an additional literature-assumption parameter.
The older `--conditional` mode checks the retained intermediate theorem and
is not the publication target. A component-only run also does not certify
the complete main theorem.

The exhaustive component audit can be lengthy. A successful source scan or
build alone is not a substitute for checking the final statement and axioms.

## Standalone packaging

This copy removes the development-only manuscript-preservation check from
`scripts/check.sh`. It does not require a sibling manuscript or research folder.
All Lean sources and all version pins are copied without changes. No Lean audit
or theorem-type check has been removed. The manuscript PDF is for reference and
is not a Lean build input.

The exhaustive unconditional audit completed in the original pinned macOS ARM64
environment. All 237 Lean files and the three build/version configuration files
in this copy match that source snapshot byte for byte. Standalone source and
import-coverage checks passed, along with packaging checks for copied-file hashes,
shell/Python syntax, shell executable permissions, relative documentation links,
and absence of bundled installation/cache directories.

A fresh full standalone rebuild has **not** been performed. The packaging checks
do not run Lean and do not establish that a new installation or another platform
will build successfully. See [the verification record](VERIFICATION.md) for the
completed audit evidence, source hashes, and outstanding publication checks.
