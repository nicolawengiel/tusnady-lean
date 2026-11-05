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

Bootstrap recognizes macOS ARM64/x86_64 and Linux ARM64/x86_64. A complete fresh
installation and verification passed on macOS ARM64 on 5 November 2026. The other
platforms have not been tested. Only the macOS ARM64 archive has a bundled
checksum, derived from the original downloaded archive.

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

A full fresh standalone test passed on macOS ARM64 on 5 November 2026, including
installation, build, exact main-statement checks, and the exhaustive axiom audit.
The documented offline check and supplemental checks also passed. The proof
sources, scripts, and version pins remain identical to the tested snapshot.
See [the verification record](VERIFICATION.md) for the tested commit, source
hashes, logs, and scope. Other operating systems have not been tested.
