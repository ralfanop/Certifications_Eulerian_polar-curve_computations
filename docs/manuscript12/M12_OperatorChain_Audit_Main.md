# Manuscript 12 — operator-chain Lean 4 audit on `main`

**Scope.** Section 5.8, especially Theorem 5.14, manuscript version of
23 November 2026, where (164) uses the inverse-cubic hybrid decay.
This report distinguishes *checked Lean proof types* from assumptions
that the author still has to instantiate for the actual infinite Jacobi
operator. It is not an assertion that the whole manuscript is unconditionally
formalised.

## Reproduce the audit

The workflow [`m12-operator-main-final-audit.yml`](../../.github/workflows/m12-operator-main-final-audit.yml)
checks out the exact `github.sha` on `main`, records it, rebuilds the pinned
Lean 4.24.0 + Mathlib dependency tree, and compiles
`lean/EulerianGrothendieck/AuditM12OperatorMain.lean`. It checks the transitive
axioms of **every explicitly listed declaration** against the standard set
`propext`, `Classical.choice`, `Quot.sound`, rejecting `sorryAx`.
The published artifact includes the commit SHA, complete build logs,
axiom report, and audit source hash.

Independent reproduced CI evidence for the existing steps:

- [#521](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/521):
  weighted energy estimate and modular conclusions (164)–(166), (160).
- [#531](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/531):
  actual betaM/profile difference and compact-uniform *conditional* rate.
- [#532](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/532):
  actual algebraic residual identity, given the classical spectral entry derivative.
- [#533](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/533):
  averaged Frechet kernel preserves pointwise PSD, symmetry, polynomial decay.
- [#534](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/534):
  exact hybrid path and FTC entrywise integration under the published derivative.
- [#535](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/535):
  hybrid residual estimate (164) from endpoint estimates (163) and locality.
- [#536](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/536):
  construct `LocalOperatorCertificate` *conditional on*
  `PublishedJacobiInput`.
- [#538](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/538):
  explicit Higham finite-spectral Jacobi bond kernel and PSD; include in this
  audit only after its exact-HEAD Lean CI has passed and it is on `main`.

## What the current Lean theorem does and does not establish

The source module
`UniformLanczos/Rate514ActualOperatorCertificate.lean`
defines `PublishedJacobiInput`; its **fields are hypotheses**, not theorems
obtained automatically from the actual Fourier/Jacobi operator. The new
`constructActualCertificate` builds a positive averaged matrix, actual
residual differences and the energy estimate *when such inputs are supplied*.

The operator literature cited in the manuscript justifies, in the classical
setting, the Daleckii–Krein/Higham finite Hermitian matrix derivative,
Fourier inversion, Duhamel identity and constant-bond diagonalisation.
However, a green Lean CI cannot alone certify all the following applications:

1. The finite eigenvector matrix and eigenvalues must be identified with the
   compression of the **actual** Jacobi operator on the segment between
   `actualBond` and `hybridBond`; then the derivative/trace identity must
   pass to the bilateral operator.
2. The instantaneous kernel's **uniform** inverse-fifth-power off-diagonal
   decay must be proved for the manuscript's smooth spectral function,
   via the Fourier/Duhamel propagation estimate. The analytic-function
   exponential-decay theorem for `f(A)` does not suffice by itself for
   `Df(J)[E_m]`.
3. The original endpoint residual bounds (163) must be specialised to the
   effective orthogonal polynomial density and to the constant-bond limit,
   with constants uniform for all large M and `j/M` in the fixed compact
   interval. The structure fields `residual_actual` and
   `residual_profile` currently carry those conditions.
4. Bond positivity, the width of the proportional window, and the
   one-size-fits-all constants (including the smallness condition
   `ε²(Cf Z3)≤4t`) must be verified on the actual proportional regime.

Consequently, the statement
`compact_uniform_rate_of_published_calculus` is a valid Lean theorem
**relative to the supplied analytical interface**; it must not be presented
as an unconditional proof of the printed Theorem 5.14 while the above
obligations remain open.

A complete claim requires a further Lean theorem that constructs the
`PublishedJacobiInput` *from the actual operator and previously proved
manuscript facts*, plus a successful audit on the exact merge commit of
`main`, with no conclusion-equivalent hypothesis.
