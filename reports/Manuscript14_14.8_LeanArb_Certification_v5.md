# Manuscript 14.8 — Lean 4 / Arb certification ledger, version 5.0

**Date:** 3 November 2026  
**Paper:** *Eulerian Fourier Profiles, Spectral Determinants, and Conformal Normalisations at the Special Point i/sqrt(2)*  
**Dedicated branch:** `special-point-i-sqrt2-cert-20261103`  
**Proof-bearing HEAD:** [`2d419774`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/2d419774dfa84e0223170b9541baadd1d8017082)  
**Kernel + Arb run:** [GitHub Actions #41716880747](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41716880747) — **SUCCESS**, both jobs  
**Previous certified checkpoint:** [#41715851347](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41715851347) — **SUCCESS**, both jobs

This register supersedes [v4](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/special-point-i-sqrt2-cert-20261103/lean/SpecialImaginaryPoint/CERTIFICATION_LEDGER_v4.md) **for the newly certified analytic assertions**, without deleting the archived statement-by-statement matrix.

## Current audited totals

| Quantity | Verified status |
| --- | --- |
| Dedicated Lean modules | **4** |
| Kernel-checked Lean declarations, explicitly audited | **22** |
| Previously kernel-checked declarations | 15 |
| New declarations in this revision | **7** |
| Arb / exact-rational checks | **37 PASS / 0 FAIL** |
| Published scalar decimals checked to 50 significant digits | 10, five at each modular companion point |
| Main printed manuscript statements | 20 (6 Theorems, 11 Propositions, 3 Corollaries) |
| Main printed statements certified in full | **0 / 20** |
| Main printed statements with partial dedicated Lean certifications | **4 / 20** |

No blanket percentage of completion is assigned. Certification of a substatement does not certify its parent theorem.

**Pinned environment:** Lean `v4.35.0-rc3`; Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`; Arb through `python-flint==0.9.0`, precision 256 bits. The Lean job's explicit axiom audit detected no `sorryAx` or `Lean.ofReduceBool`. The enumerated proofs use only `propext`, `Classical.choice`, and `Quot.sound` (or subsets).

## Newly certified analytic content

Module: [`lean/SpecialImaginaryPoint/BorelAnalyticConvergence.lean`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/2d419774dfa84e0223170b9541baadd1d8017082/lean/SpecialImaginaryPoint/BorelAnalyticConvergence.lean)

For `c_n=4^n/(2n+1)!` and `F(t)=∑_{n≥0} c_n t^n` the kernel has certified:

1. `eulerianEntireSeries_summable` — summability for **every** `t:ℂ`, via the norm-majorant exponential series.
2. `eulerianEntireSeries_hasSum` — the actual complex function is the sum of those terms.
3. `eulerianEntireSeries_hasFPowerSeriesAt_zero` — the specified Taylor expansion represents `F` as an analytic germ at zero.
4. `eulerianEntireSeries_analyticAt_zero` — complex analyticity at zero.
5. `eulerianEntireSeries_radius_top` — the formal multilinear scalar series has radius `∞`.
6. `eulerianEntireSeries_hasFPowerSeriesOnBall` — the Taylor expansion represents `F` on the **entire complex plane**.
7. `eulerianEntireSeries_analyticAt` — `∀z:ℂ, AnalyticAt ℂ F z`.

The comparison underlying this result is the exact factorial inequality `n! ≤ (2n+1)!` and the exponential bound `∑ₙ |c_n t^n| ≤ exp(4|t|)`. Radius and global analytic expansion are kernel-checked, not merely inferred from numeric sampling.

## Relationship with printed Theorems 3.3 and 3.5

- **Theorem 3.3** (Exact Borel–Eulerian specialisation): its output series is now certified to be entire. Its full equality with the printed `{}_0F_1`, hyperbolic-sine and Eulerian sine-cardinal expressions is **not yet fully Lean-certified**.
- **Theorem 3.5** (Differential-operator identity under double Borel transform): the formal identity `L_F ∘ B² = θ ∘ B² ∘ L_A` on `PowerSeries ℂ` was already certified in v4. The newly certified global analytic output strengthens its analytic prerequisite. The entire *printed* theorem remains **PARTIAL** pending the exact kernel-checked bridge from formal derivatives to analytic derivatives, the analytic input `A(t)` on its disk of convergence, and both ordinary differential equations.

The earlier partial status of Corollary 2.3 and Proposition 3.1 is unchanged. In particular, no entire manuscript theorem should be reported as certified merely because a central lemma has been certified.

## Arb numerical boundary

The same successful run executed **37/37** numerical checks (five accurately rounded 50-significant-digit scalar quantities at each of `i/sqrt(2)` and `i*sqrt(2)`, exact low-order zeta coefficients, the denominator recurrence sample, rational remainder bounds, and high-precision CM checks around 8000). No Arb check certifies an infinite-dimensional operator statement or the exact modular identity `j=8000` in Lean.

## Next formal obligations — in dependency order

1. Certify the analytic input `A(t)` for `|t|<1` with its exact reciprocal-central-binomial coefficients.
2. Connect `PowerSeries.derivative` and `FormalMultilinearSeries.derivSeries` to the derivatives of the globally analytic function `F`; prove the coefficient recurrence and the analytic ODE `tF'' + (3/2)F' - F = 0`.
3. Prove the analytic equality `F=B² A`, then `L_A A=1/2` and the Gauss differential equation on `|t|<1`.
4. Finish the remaining special-value and pullback identities, with domain and parameter normalization matched to the manuscript's exact text.
5. Continue with the other main results in the archived 20-row statement matrix; do not duplicate general results of manuscripts 11–13.

No merge was performed to PR #16, V007, V097 or the repository's main branch. Manuscipts 11–13 were not changed.
