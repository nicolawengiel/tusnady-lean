# Reused formal proofs

Selected proofs from [Per Alexandersson et al., RealRooted](https://github.com/PerAlexandersson/RealRooted)
are included under `Tusnady/External/RealRooted/` for the sampling argument.

- Upstream revision: `5fd4a62e271bc8eadc3b2f64c18fd4c1e734a837`.
- License: [Apache-2.0](../Tusnady/External/RealRooted/LICENSE).
- Original paths and revision information are preserved in the source headers.
- The selected files were ported to this project's pinned Lean/mathlib 4.24.0;
  the upstream project's toolchain and dependency configuration are not imported.
- Adaptations include module syntax and API changes, explicit splitting maps,
  and finite-type matrix interfaces. Unneeded sections were omitted.

Original namespaces are retained. `Audit.lean` recognizes these proofs by their
defining modules, so the component audit includes the reused proofs even where
their namespaces are `RealRooted`, `Polynomial`, or `MvPolynomial`.

This publication copy preserves the original copyright, license, and attribution
notices. The local research checkout and compiled caches are not release inputs.
