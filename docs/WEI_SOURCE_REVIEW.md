# Wei's planar lower bound

Zhewei Wei proved the sharp lower bound in the plane in
[*Tight Bounds for Tusnády's Problem in the Plane*](https://arxiv.org/abs/2610.08130).
This project reuses his Lean formalization, version `r65-submission-v2`,
at [revision `6f14d177668e79a9155f7cd60496313514ad0c9e`](https://github.com/wzskytop/tusnady-lean/tree/6f14d177668e79a9155f7cd60496313514ad0c9e).
His software retains its [MIT license](../vendor/wei-6f14d177/LICENSE),
copyright 2026 Zhewei Wei.

The integration builds the 83 modules imported by
[`R56Audit.Parameters`](../Wei/R56Audit/Parameters.lean). Their mathematical
namespaces and proof bodies match the upstream source. The active modules
carry local `Wei.` import paths and an attribution header. The
[source manifest](../vendor/wei-6f14d177/provenance.json) identifies each
upstream file by path and hash. The [vendor check](../scripts/verify_wei_vendor.py)
verifies the frozen originals and reconstructs each active module's upstream
contents from its locally adapted copy.

The import used for Tusnády's problem is `R56Audit.exists_points`. It gives
an injective configuration in the unit square such that every coloring by the
integer units attains Wei's lower bound. [WeiAudit.lean](../WeiAudit.lean)
checks its exact type and dependencies together with the probabilistic theorem
`R56Audit.theorem_1_1_unfolded` and the deterministic corollary
`R56Audit.corollary_1_2_lower`.

The [coordinate and coloring lemmas](../Tusnady/PlanarWei/Coordinates.lean)
convert pairs of real numbers into `Point 2` and each real ±1 coloring into
an integer-unit coloring with the same values. For these nonnegative points
the counts in Wei's closed anchored rectangles agree exactly with counts
in closed lower orthants. The [lower-bound module](../Tusnady/PlanarWei/LowerBound.lean)
chooses the base in Wei's estimate before `N` and absorbs the change from
base-two to natural logarithms into one positive constant. The resulting
`Tusnady.PlanarWei.planar_lower_bound` holds for every integer `N ≥ 1`.
