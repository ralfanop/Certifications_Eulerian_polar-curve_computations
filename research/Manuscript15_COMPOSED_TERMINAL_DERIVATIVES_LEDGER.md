# Manuscript 15 — Composed terminal convolution derivative classification

**Stacked integration branch** based on PR #191, which already formally
defines the M-fold convolution coordinates and proves their endpoint
positions. It imports **exact copies of the independently
kernel-certified source files** from PR #203
(`TerminalPowerJet.lean`) and PR #204
(`EulerianRootDerivatives.lean`), and adds the explicit Lean library
target necessary to import cross-module prerequisites.

The five new declarations prove, for every a∈ℝ and natural
convolution order M:
- exact differentiability of t↦r_E(2t) at t=2π;
- when M≥2, `HasDerivAt X_M a (2π)`;
- when M≥1, `HasDerivAt Y_M 0 (2π)`;
- corresponding exact `deriv X_M (2π)=a`;
- `deriv Y_M (2π)=0`.

This is the **genuine terminal tangent calculation** for all M≥2,
not merely a formula at abstract zeros.

**Remaining:** the M=1 singular cycloid terminal case (derivative
zero), the higher-order contact/jet classification, and source
measure-level convolution statements.

**Status:** integration candidate until *combined* Lean
library build and exact-head kernel-axiom CI succeeds.
Even though the three prerequisite files have passed isolated CI,
their composition is not asserted certified before that run.
The pull request targets the PR #191 branch instead of main to keep
the dependency explicit; no merge is performed.


## Complete classification extension (new executable head, pending CI)

The source now imports the previously kernel-certified `CycloidalReconstruction.lean` and includes five additional statements: the singular `M=1` derivative, the piecewise `M≥1` X-derivative classification, the full planar velocity pair, explicit M=1 stationarity, and regular nonzero terminal velocity for M≥2 when a≠0. These are **new declarations requiring a fresh combined exact-head CI**. The original successful integration run applied only to the five M≥2 derivative statements.
