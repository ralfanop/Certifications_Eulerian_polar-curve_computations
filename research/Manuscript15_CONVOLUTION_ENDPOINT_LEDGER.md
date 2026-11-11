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
