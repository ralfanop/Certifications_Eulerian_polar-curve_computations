# M16.6 §13: exact rational tail for the scalar p=4 shell sum (19 Nov 2026)

**Status:** analytic scalar estimate only; not a Lean theorem, not an Arb certificate, and not a Maxwell–Dirac operator result. Does not change any frozen manuscript.

Define for integers ell>=2 and k in Z except 0,-ell:

- d(ell,k) = |ell²-(ell+2k)²| = 4|k||ell+k|;
- g(ell) = 2(ell²-1);
- S4 = sum_(ell>=2) g(ell) sum_(k≠0,-ell) d(ell,k)^(-4);
- T4(N) = sum_(ell>N) g(ell) sum_(k≠0,-ell) d(ell,k)^(-4), N>=2.

**Exact inequality:** 0 <= T4(N) <= 53/(96 N).

Proof: j=min(|k|,|ell+k|)>=1 and max(|k|,|ell+k|)>=ell/2, so d>=2ell j. At most four k have a given j, yielding

sum_(k≠0,-ell) d^(-4) <= 4/(2ell)^4 sum_(j>=1) j^(-4).

The elementary rational bound (no numerical zeta evaluation)

sum_(j>=1) j^(-4) = 1+1/16+sum_(j>=3)j^(-4)
<= 1+1/16+integral_2^infinity x^(-4) dx = 53/48

follows from monotonicity. Since g(ell)<=2ell², the ell-shell is bounded by
(1/2)(53/48)ell^(-2)=53/(96 ell²).
Finally sum_(ell>N)ell^(-2) <= integral_N^infinity x^(-2)dx = 1/N.

The upper bound is a rational inequality for an infinite nonnegative series, **not** a finite-window numerical check. It provides a rigorous absolute tail enclosure for the scalar sum, usable in a later Arb evaluation. It is not a proof of 3,400,000 relative bits or 1,000,001 correctly rounded significant decimal digits.

**Formalization obligations:** (1) define integer index set and nonnegative summands in Lean; (2) prove the four-preimage shell count; (3) establish summability and the exact tail inequality; (4) only then relate the scalar series to actual singular values after proving spectral completeness, multiplicities and operator domains. No physical identification follows from this note.

**Provenance:** analytic derivation for the frozen v16.6 §13 spectral shell model; must be reconciled against the exact frozen equation labels before marking any equation certified. Historical PR #403 is the reconciliation reference; PRs #405–#406 concern abstract operator approximation and do not establish this scalar tail theorem.
