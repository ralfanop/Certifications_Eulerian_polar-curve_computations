# Manuscript 16 v16.4 §13 — scalar Schur factor audit

Authoritative source: `Manoscritto_16_4_Editorial_Abstract200_Sezioni14-16_20261114(1).zip`, SHA-256 `c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f`.

Theorem `thm:dirac-maxwell-obstruction-164`, formula `eq:mixed-factor-164` is an operator factorisation on graph domains. This independent PR proves **only** its finite-dimensional scalar determinant counterpart, for real `a,b,c,l` and `l != 0`:

```
a*l-b*c = (a-b*l^(-1)*c)*l
a*l-b*c != 0 iff a-b*l^(-1)*c != 0.
```

Lean 4 file: three algebraic propositions, with `#print axioms` and a pinned CI workflow. No Arb is required: all statements are exact rational/algebraic identities. Do not attribute any relative precision or significant digits to them.

**Still open:** bounded invertibility on graph domains; compactness of `B L^{-1} C`; Atkinson Fredholm equivalence and index; the `det_4` criterion. This branch is disjoint from the M16 Neumann-gap PR #322 and M14/M15 work. Historical numerical certificates remain untouched. Review the exact HEAD CI before calling these three lemmas certified; do not merge automatically.
