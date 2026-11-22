# Manuscript 15 -- companion Lean 4 development (22 November 2026)

Formalises the statements of Manuscript 15 that were still pending:

| Statement | Module |
|---|---|
| Proposition 7.25 (catenoid: Eqs. (287)-(291), vanishing mean curvature) | `Kernel`, `Catenoid` |
| Theorem 7.26 (Carlini-Laplace normalisation, unique maximum, tangent bicone, (292)-(295)) | `CarliniLaplace` |
| Proposition 7.27 (Ellis metric, proper radial length, (297)-(300)) | `EllisMetric` |
| Theorem 7.19 (identification of the triangular density) | `TriangularDensity` |
| Eq. (262) (principal-root formulation) | `PrincipalRoot` |
| Eq. (267) (stability inequality) | `Stability` |
| Proposition 7.22, Eqs. (275)-(277) of version 39 (period-two disc, tangency with the cardioid; added 22 November 2026) | `PeriodTwo` |

* Toolchain: `leanprover/lean4:v4.35.0-rc3`; Mathlib tag `v4.35.0-rc3`
  (commit c55e6e786f49471c72fbddbec5415808896aec1e), pinned in `lake-manifest.json`.
* Library `M15Cert`, namespace `M15`; depends only on Mathlib. The private development
  (PrivateApex) is neither imported nor modified; to merge, the modules can be copied under
  its root and `M15.rEc`, `M15.rE`, `M15.eulerianB`, `M15.cMand` identified with the
  corresponding definitions there.
* `axioms_output.txt`: `#print axioms` for 68 theorems (`M15Cert/Axioms.lean`); all depend only
  on `propext`, `Classical.choice`, `Quot.sound`.
* `leanchecker_output.txt`: `leanchecker` exit 0 on each of the eight modules.

Reproduce:

```
lake exe cache get
lake build
lake env lean M15Cert/Axioms.lean
for m in Kernel PrincipalRoot Stability TriangularDensity Catenoid CarliniLaplace EllisMetric PeriodTwo; do
  lake env leanchecker M15Cert.$m; done
```
