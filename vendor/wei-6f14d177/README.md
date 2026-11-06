# Frozen Wei software reference

Author: Zhewei Wei. Software copyright (c) 2026 Zhewei Wei.
Repository: <https://github.com/wzskytop/tusnady-lean>.
Frozen commit: `6f14d177668e79a9155f7cd60496313514ad0c9e`.
License: MIT; the unmodified license is provided as `LICENSE` and
`original/LICENSE`.

This directory retains software only. No manuscript PDF, TeX file, rendered
manuscript HTML, or manuscript-license document is included. The supplied
software README and audit documents refer to their original manuscript, but
those references do not import or redistribute the manuscript itself.

The 125 original software files were fetched from this exact public commit.
Every downloaded file was checked against its Git blob SHA-1 from the complete
GitHub tree and is recorded with SHA-256 in `provenance.json`. Original Lean
sources have suffix `.lean.txt` so that they cannot accidentally become Lake
source roots. Their bytes are unchanged. Software scripts have not been run.

The 83 required active source modules are separately provided under `Wei/`.
Only project-local import names are prefixed with `Wei`; mathematical
namespaces and proof bodies are unchanged. A MIT/commit header is added to each
active file. All changes and hashes are recorded, and reverse-normalization
was checked against every original. `Wei.lean` imports the primary interface.

The authoritative primary interface is `R56Audit/Parameters.lean`:
`R56Audit.theorem_1_1_unfolded`, `R56Audit.exists_points`, and
`R56Audit.corollary_1_2_lower`. `Oscillation.paper_lower_bound` is a historical
comparison proof. Importing a module that contains it is distinguished from
actually using its proof term; the latter must be independently audited.

The upstream toolchain is Lean 4.34.1 with mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, matching the new integration target.
The independent local build is now complete: the exact-option Lean 4.34.1
build of `Tusnady.PlanarWei.LowerBound` passed with 3860 jobs. `WeiAudit.lean`
compares all three actual declaration types against independently written
formulas and checks their complete kernel dependency closures. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; the primary proof route is present
and the historical comparison route is absent. The endpoint is
`WEI COMPLETION STATUS: COMPLETE`.

`provenance.json` records the local evidence and hashes explicitly. The
reproducible commands are `python3 scripts/verify_wei_vendor.py`,
`./scripts/lake.sh build Tusnady.PlanarWei.LowerBound Tusnady.Audit.Dependencies`,
and `./scripts/lake.sh env lean WeiAudit.lean`. A public upstream report was
not substituted for the independent local build or recursive axiom audit.

See `../../docs/WEI_SOURCE_REVIEW.md` for exact source statements, full import
closure, scanner limitations, and the bridge plan to our unchanged discrepancy
definitions. Nothing in this directory is a release or a publication action.
