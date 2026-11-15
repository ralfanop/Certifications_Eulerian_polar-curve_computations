# M16 v16.4 §13 — Neumann-gap scalar bridge

Authoritative source: `Manoscritto_16_4_Editorial_Abstract200_Sezioni14-16_20261114(1).zip`
SHA-256: `c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f`.

Scope: Proposition `prop:mixed-schatten-164`, equation `eq:mixed-inverse-bound-164`.
The manuscript states `||L0^-1|| = 2/3` and `||E|| < 3/2`.
With `e = ||E||`, the scalar Neumann ratio `(2/3)e < 1`.
The four Lean declarations establish positivity of `3/2-e`, strict
Neumann margin, exact equality

```
(2/3) / (1-(2/3)e) = 1/(3/2-e),
```

and positivity of the right-hand side.

**Scope boundary:** The proof of operator factorisation
`L=(I+E L0^-1)L0`, invertibility of `I+E L0^-1`,
the Banach-space Neumann bound, graph-domain equality and Schatten
stability remain *analytic* obligations. The scalar identity alone
does not certify the full proposition.

**Numerical precision:** No FLINT/Arb run required: every new result
is an exact identity/inequality over real variables, not an enclosure
of a nonzero transcendental quantity. In particular, no claim of
3,400,000 relative bits or 1,000,001 significant digits is made here.

**Repository workflow:** This branch is independent of M14/M15 and
the M16 finite-cutoff branch. Review exact HEAD and CI; do not merge
without review. Historical numerical certificates remain unchanged.
