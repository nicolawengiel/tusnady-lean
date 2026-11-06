# Frozen analytic source reference

Repository: https://github.com/openai/math

Commit: `4eaee87548250b2682affda7d05d947c05554bae`.

The `original/` files (stored with extension `.lean.txt`) are the complete upstream OAI import closure of
`GaussianPropeller/SmoothedConcavity.lean` and `ConeConcavity.lean`. They are
retained for attribution and reproducible review. They are not Lake source
roots and are not imported by the Tusnady project. Upstream uses Lean 4.34.1;
the project ports selected proofs to its existing pinned Lean 4.24.0.

The Apache-2.0 license is included. `provenance.json` records SHA-256 digests
of each original source. Ported modules under `Tusnady/Upper/Ehrhard/` remove
unrelated imports and use the project's actual product Gaussian measure.

A source scan of this complete 14-module closure found no `sorry`, `admit`,
axiom, opaque declaration, unsafe definition, native proof oracle or
`implemented_by` annotation. This is source-review evidence, not a substitute
for the kernel checks of the ported modules. The smooth heat-concavity lemma
still requires its displayed smoothness, derivative-bound and concavity
hypotheses. They are analytic foundations, not a pre-existing proof of this
project's complete fold comparison. The additional project proofs now derive
small-radius fold monotonicity and close the upper main theorem with universal
signing factor 1000. The separate exact radius-1/5 proposition remains optional
and is not used by `Tusnady.Upper.Main`.

The manifest lists all eight ports, `AffineSoftMinimum` as a derived extension,
and the remaining project-native analytic modules. It also records their
post-freeze SHA-256 digests. The fourteen retained original source hashes were
rechecked and match exactly. See `docs/UPPER_LITERATURE_AND_PROVENANCE.md` for
precise statement hypotheses, source roles, and the distinction between the
proved factor-1000 route and the unused exact-factor-5 route.
