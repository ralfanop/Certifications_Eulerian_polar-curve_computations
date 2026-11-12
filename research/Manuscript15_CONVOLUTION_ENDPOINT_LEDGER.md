# Manuscript 15 — Convolution endpoint coordinates

Six new Lean declarations, conditional on successful exact-head CI:
- exact Eulerian kernel zero at 2π;
- exact Eulerian kernel zero at 4π;
- X_M(2π) = 2πa for every positive integer M;
- Y_M(2π) = 0 for every positive integer M;
- X_M(0) = 0;
- Y_M(0) = 0.

Reuses the genuine `EulerianCert.FourierModes.rE` from Manuscript 11. The source defines the manuscript's M-fold convolution coordinates exactly, and the pinned workflow builds the inherited Eulerian kernel.

**Not yet established:** the derivative classification `(X'_M(2π),Y'_M(2π))`, local contact order, t→0 limits and absolute geometric curvature. This PR certifies only the endpoint **position** equations, not the full theorem.

No change to Manuscripts 11–14 or V007/V097; no merge.


## Exact-source CI success (verified)

[GitHub Actions run #43178039574](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43178039574) completed **SUCCESS** for executable source commit `b0e40c462f1f6c3d9b2aba56ef41412931669a91`. Six inherited Eulerian zero, origin and convolution endpoint-position declarations kernel-checked. Terminal derivatives and contact orders are separate. The workflow explicitly checks the Lean kernel and audits for `sorryAx` and `Lean.ofReduceBool` (or, for the full Eulerian table, asserts outward interval accuracy).

This is a historical immutable-source verification record. A documentation-only later commit does not change the executable source; any subsequent executable revision must be checked on its own exact commit before certification is transferred.
