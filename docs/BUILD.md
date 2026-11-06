# Reproduce the v0.2.0 verification

From the repository root, run `./scripts/bootstrap.sh` and then
`./scripts/check-integrated.sh --standalone`. A first installation needs
network access, Git, Python 3, curl, ripgrep and tar with Zstandard support.
The bootstrap installs Lean 4.34.1 locally and retrieves the nine pinned Git
dependencies. It fetches the compiled mathlib cache. The project itself builds
locally. After the first bootstrap, `./scripts/bootstrap.sh --offline` checks
the existing installation.

The standalone option permits historical files outside the checkout to be
absent. It runs the mathematical checks, including the checks for the
upper and lower bounds, Wei's result and the combined theorem.
See the [release verification records](release-v0.2.0/README.md).
