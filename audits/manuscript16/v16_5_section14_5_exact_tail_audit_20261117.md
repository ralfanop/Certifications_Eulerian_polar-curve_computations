# M16 v16.5 §14.5 — independent exact-tail audit (2026-11-17)

**Source lock.** Author-approved ZIP `Manoscritto_16_5_Magnetic_Evanescent_Spectral_Transport_20261116(1).zip`, SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`. No manuscript source is modified.

**Scope.** Theorem 14.5, exact discrete-tail identity and a rigorous obstruction to bounded-displacement couplings. This is an analytic audit, **not** a Lean certification or FLINT/Arb certificate.

Set `0 < q < 1`, `w_n = 4(n+1)(n+3)`, and `C(q) = sum_{n>=0} w_n q^n = 4(3-q)/(1-q)^3`. Define magnetic index law `p_n=(1-q)q^n` and Maxwell index law `r_n=w_n q^n/C(q)`. Both are probabilities.

For every integer `N>=0`, expanding `w_{N+k}/4 = (N+1)(N+3)+(2N+4)k+k^2` and applying the three convergent geometric moment identities gives the **exact upper tail**

```text
sum_{n>=N} r_n
 = 4*q^N/C(q) * (
      (N+1)*(N+3)/(1-q)
      + (2*N+4)*q/(1-q)^2
      + q*(1+q)/(1-q)^3 ).
```

In particular, the magnetic upper tail equals `q^N`, while the ratio of Maxwell to magnetic upper tails diverges quadratically in `N`.

**Bounded-displacement contradiction.** Suppose a coupling `(X,Y)` of the index laws satisfies `|X-Y| <= M` almost surely, for a finite integer `M>=0`. For every `N>=M`, `{Y>=N} subset {X>=N-M}` almost surely. Consequently,

```text
4/C(q) * (
 (N+1)*(N+3)/(1-q)
 +(2*N+4)*q/(1-q)^2
 +q*(1+q)/(1-q)^3
) <= q^(-M).
```

The left-hand side diverges quadratically with `N`; the right-hand side is constant. Contradiction. Therefore every coupling has unbounded essential displacement, and `W_infinity=+infinity` on the energy axis `E_n=2n+1` as well.

**Lean obligations (unproved here):** (i) geometric sums for `q^k`, `k*q^k`, `k^2*q^k`; (ii) nonnegative termwise rearrangement and tail formula; (iii) probability normalization; (iv) coupling marginal event inequality; (v) polynomial divergence; (vi) energy-axis scaling. Do not replace (iv) with a statement about pointwise mass or assume a coupling exists with finite displacement.

**Numerical status:** no Arb run; no claim of 3,400,000 certified relative bits or 1,000,001 certified significant decimal digits. All coefficients in the displayed algebraic identities are exact integers/rationals, so no floating-point certification is required for the identities themselves.

**Separation:** this note does not identify Wasserstein transport with electromagnetic energy flux or physical spatial transport. Avoid duplication with the M15 transport PRs; this concerns the specific Maxwell multiplicity polynomial of M16 §14.5.
