# M16 v16.5 §14.5 scalar Gibbs audit — 2026-11-17

Source: author-approved ZIP SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`. No source manuscripts modified.

## Scope
Theorem `mean_difference_rational` isolates the rational simplification of the difference between two **index means**, with explicit nonzero denominators. It is a candidate Lean proof, not a full Wasserstein theorem.

## Independent obligations not discharged
1. Exact generating functions and finite first moments of both Gibbs distributions.
2. Stochastic dominance via increasing size bias and covariance (or explicit tails).
3. Existence of monotone coupling and identification of optimal W1 with difference of means.
4. W_infinity obstruction, addressed analytically in PR #341.
5. Operator/physical interpretations are outside this scalar statement.

## Verification
Lean/Lake not available in local environment at authoring time. No CI success claimed, no `#print axioms` output. No FLINT/Arb numerical certification performed: exact rational algebra needs no floating-point accuracy, and no million-digit claim is made.

## Avoid overlap
PR #342 gives analytic W1 bounds; this file isolates the rational algebra underlying the **exact formula already stated in the authoritative manuscript**, without replacing or modifying #342.
