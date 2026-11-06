# Independent rebuild of the integrated proof

**Passed.** The checked candidate came from commit `2896887242bab9f66071cce72127474b1ad42937` using Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The rebuild finished at 18:33 UTC on 5 November 2026. The source tarball, `tusnady-0.2.0-rc1-2896887242ba-source.tar.gz`, had SHA-256 `fadf30fbdfa9f140c8572c1bf2441c4f2a1f3d668996e34975c1fce6835bc468`.

All 683 files in the candidate matched the archive, recorded Git blob IDs and SHA-256 values both before and after the checks. The archive supplied 412 Lean sources, including the six audit files. A fresh directory had no project build cache. The run reused the installed Lean runtime and nine pinned dependency trees and their compiled caches, all on the same machine. All project modules were built from source.

The following commands each exited successfully. The default build ran 4,251 jobs. Across the main and supplementary checks the run generated fresh `.olean` files for all 406 non-audit project modules and executed all six audit files.

```sh
env -u LEAN_PATH -u LEAN_SRC_PATH ./scripts/lake.sh build
env -u LEAN_PATH -u LEAN_SRC_PATH ./scripts/check-integrated.sh --standalone
env -u LEAN_PATH -u LEAN_SRC_PATH ./scripts/lake.sh build Tusnady.External.RealRooted.Mathlib.Analysis.Complex.OpenMapping
env -u LEAN_PATH -u LEAN_SRC_PATH ./scripts/lake.sh env lean LiteratureAudit.lean
```

The reports record 15 exact integrated theorem types, 6,228 imported project theorems and 6,246 entries in the integrated axiom audit. The recursive dependencies of `Tusnady.Integrated.main_sharp_order` cover 69,201 constants. The audit reported only `propext`, `Classical.choice` and `Quot.sound`. Together the main statements give sharp discrepancy for closed lower orthants and bounded closed axis-parallel boxes in every fixed dimension at least two.

Standalone mode recorded the absence of 1,281 files from the previous working directories and 15 external manuscript files. Type checks, Lean builds and axiom checks all ran, including a digest comparison for the local definitions of discrepancy. The accompanying JSON contains the command outcomes, installed dependency revisions, source digests and the additional coverage of the open-mapping and literature modules.

This English report accompanies the public edition of the rebuild evidence. The package README explains the changes to filesystem paths in the JSON and why the public and original bundle digests differ.
