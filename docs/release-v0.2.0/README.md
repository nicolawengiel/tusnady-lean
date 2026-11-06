# Verification records for v0.2.0

The [independent rebuild report](independent-rebuild-2896887242ba.md) records the check of the Lean sources used for this release. They were extracted from the source archive of the integrated release candidate, whose local Git commit was `2896887242bab9f66071cce72127474b1ad42937`. The archive contained 683 files, including all 412 Lean source and audit files. On 5 November 2026, the project build, both supplementary checks and the standalone audit finished with exit code 0. The [release source comparison](release-source-comparison.json) lists the SHA-256 of each of the 412 Lean files shared by the verified candidate and this release. It also records the build scripts, pinned dependencies and the Lake package version change.

The combined theorem gives the sharp discrepancy order for closed lower orthants and bounded closed axis-parallel boxes in each fixed dimension at least two. The audit checked the exact types of 15 main declarations and the transitive axiom dependencies of the combined result. All 406 regular Lean modules were built from source in a fresh project directory. The Lean 4.34.1 runtime and compiled caches of nine pinned third-party dependencies were reused.

## Files

* The [rebuild attestation](independent-rebuild-2896887242ba.json) identifies the archive, Git tree, dependency pins, checked theorem names, commands, exit codes and the checksums of individual proof sources. Its publication fields describe the candidate at the time of the build.
* The [fresh module inventory](independent-rebuild-2896887242ba-modules.json) lists the source and compiled module checksums. The [audit log archive](independent-rebuild-2896887242ba-logs.tar.gz) contains all 13 original log files, byte for byte, in `logs/`, together with the public copy of this inventory. The [default build](independent-rebuild-2896887242ba-default-build.log), [standalone audit](independent-rebuild-2896887242ba-standalone-complete.log) and [final integrity check](independent-rebuild-2896887242ba-final-integrity.log) are also available as individual logs.
* The [source package attestation](tusnady-0.2.0-rc1-2896887242ba-source.attestation.json) identifies every file in the tested candidate, its Git blob and SHA-256. The [packaging repeat](tusnady-0.2.0-rc1-2896887242ba-source.reproducibility.json) records a second, byte-identical packaging of the candidate. Both files are exact copies of the original records. The tested candidate tarball and ZIP have SHA-256 `fadf30fbdfa9f140c8572c1bf2441c4f2a1f3d668996e34975c1fce6835bc468` and `38109a44be57407b4ccf361f5ccef50a0ccaec0e026a7165b655ef6ed7699698`, respectively. GitHub and Zenodo distribute the tagged release with its public documentation and metadata.
* [SHA256SUMS](SHA256SUMS) lists the checksums of the public files in this directory. [ORIGINAL-SHA256SUMS](ORIGINAL-SHA256SUMS) preserves the checksums and filenames of the original internal delivery, including the candidate archives. Its paths are relative to the directory that held that delivery.

## Reproducing the checks

From the root of a clean copy of the tagged project, run:

```sh
./scripts/bootstrap.sh
./scripts/lake.sh build
./scripts/check-integrated.sh --standalone
```

The report also gives the two supplementary commands. Build times and dependency downloads depend on the machine. The logs, module inventory and attestation above record the run on the tested candidate. The documentation at the [repository root](../../README.md) describes the release.

To verify the public evidence payload, change to this directory and run `shasum -a 256 -c SHA256SUMS` or `sha256sum -c SHA256SUMS`. The SHA-256 values under `log_artifacts` in the rebuild attestation verify the individual files after unpacking the log archive.

The [public release check](public-main-check.json) records a further execution of the combined main audit using the final release files and compiled proof modules from the independently rebuilt candidate.

## Public edition of the rebuild evidence

The report is an English account of the original rebuild under its original filename. The rebuild JSON and module inventory use the labels `<fresh-parent>`, `<fresh-project>` and `<original-workspace>` for machine-specific paths. Evidence filenames are relative to this directory. The log archive was repacked to include the sanitized inventory, preserving every individual log byte. Only the public sizes or hashes of modified evidence files were updated in the rebuild JSON. Its `original_sha256` fields retain the prepublication values for the report, inventory and log archive. All proof source hashes, axiom records, command outcomes and individual log checksums retain their original values.
