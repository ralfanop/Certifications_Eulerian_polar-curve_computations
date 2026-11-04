# Manuscript 14.1 — Corollary 3.6 analytic completion certificate

**Verified on 2026-11-04.** This record concerns **Corollary 3.6 only**, not the whole manuscript.

## Certified source and CI

- Source commit (exact SHA): `0a645379268bf09189e4bec358286515019bb13f`
- [Isolated Lean 4 + Arb GitHub Actions run #41824974185](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824974185): **SUCCESS**.
- Both jobs completed successfully: `Kernel check / axioms — Corollary 3.6` and `Arb / exact Q — Corollary 3.6`.
- [Certified Lean source](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/0a645379268bf09189e4bec358286515019bb13f/lean/SpecialImaginaryPoint/Corollary36Analytic.lean).
- Dependencies: `Corollary36.lean`, `FormalBorelComplex.lean`, `BorelAnalyticConvergence.lean` at the same source revision.

## Mathematically formalized

Let
`F(t) = ∑_{n≥0} (4^n/(2n+1)!) t^n` and `r_E(z) = F(-z²/16)`.
The pinned Lean kernel accepted the following theorems:

1. `eulerianEvenAnalytic_mul_eq_sin`: `(z/2) F(-z²/16) = Complex.sin(z/2)` for every complex `z`.
2. `eulerianEvenAnalytic_eq_sinc`: `F(-z²/16)` is the regularized complex sinc, equal to `sin(z/2)/(z/2)` when `z ≠ 0`, and `1` when `z=0`.
3. `eulerianEvenAnalytic_analyticAt`: the analytic pullback is complex analytic at every `z`.
4. `eulerianEvenAnalytic_deriv_relation`: `r_E(z)+z*r_E'(z)=cos(z/2)`.
5. `eulerianEvenAnalytic_second_deriv_relation`: `2*r_E'(z)+z*r_E''(z)=-sin(z/2)/2`.
6. `eulerianEvenAnalytic_differential_eq`: `z²*r_E''(z)+2*z*r_E'(z)+(z²/4)*r_E(z)=0` for **every** complex `z`, including `0`.

The earlier module `Corollary36.lean` proves the universal operator identities on corrected formal power-series domains. The analytic identity and true derivative equation above close the remaining analytic link.

## Audit

The `#print axioms` outputs for all six new theorems list only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or `Lean.ofReduceBool` occurs in their dependencies.

The Arb job at 256-bit precision also succeeds for the independent finite exact-rational regressions and rigorous special-point enclosures. Numerical tests do not replace the universal Lean proof.

## Scope and publication boundary

- No changes to the older manuscript V007 or V097 are implied.
- This branch has not been merged into `main`.
- The certificate is tied to the exact code commit above; later edits require a fresh CI check.
