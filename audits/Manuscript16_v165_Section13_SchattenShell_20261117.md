# M16 v16.5 §13 — independent audit of the sharp Schatten shell threshold

Source lock: author-approved ZIP SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`. This file is an **analytic audit**, not a Lean certificate or Arb numerical certificate. It does not modify any manuscript.

## Exact integer shell lemma

Fix an integer `ell >= 2`. For every integer `k != 0,-ell`, put `j(k)=min(|k|,|ell+k|)`, a positive integer. Then

1. `|ell^2-(ell+2*k)^2|=4*|k|*|ell+k|` exactly;
2. `max(|k|,|ell+k|)>=ell/2` by the triangle inequality;
3. hence `|ell^2-(ell+2*k)^2|>=2*ell*j(k)`;
4. for each fixed positive integer `j`, the equation `j(k)=j` has at most four integer solutions: they lie in the union `{j,-j,-ell+j,-ell-j}`. Coincident values only improve the bound.

For `p>1`, these four facts imply
```
sum_{k in Z, k != 0,-ell} |ell^2-(ell+2*k)^2|^(-p)
 <= 4*(2*ell)^(-p)*zeta(p).
```
This is a nonnegative-series comparison, not a finite algebraic identity. The transverse multiplicity `d_ell=2*(ell^2-1)` then gives convergence of the Maxwell contribution when `p>3`, since `sum_{ell>=2} ell^(2-p)` converges.

For the reverse implication, restrict to the legitimate single temporal mode `k=1` (i.e. `m=ell+2`):
```
sum_{ell>=2} 2*(ell^2-1) / (4*(ell+1))^p.
```
Its terms are asymptotic to `2*4^(-p)*ell^(2-p)`, so it diverges for every real `p<=3`. In particular no use of `zeta(p)` is required in the divergent regime. Together with the spatial Dirac summand this proves the analytic equivalence `L0^{-1} in S_p iff p>3` for the operator and multiplicities specified in the source.

## Bounded perturbation and domain obligation

On the *unchanged graph domain* `Dom(L)=Dom(L0)`, if `E` is bounded and `||E||<3/2`, write `B=I+E*L0^{-1}`. Then `||E*L0^{-1}||<1`, so `B` is boundedly invertible and `L=B*L0`. Consequently `L^{-1}=L0^{-1}*B^{-1}`, and conversely `L0^{-1}=L^{-1}*B`. The two-sided ideal property of `S_p` proves **both directions** of Schatten membership. The inverse bound follows from the Neumann series:
`||L^{-1}|| <= (2/3)/(1-(2/3)||E||)=1/(3/2-||E||)`.

## Formalization obligations

A. Integer-index finite shell lemma, without analytic axioms.

B. Nonnegative series comparison and p-series convergence/divergence, for real `p>0`.

C. Multiplicity and spectral decomposition of the exact Maxwell/Dirac operators, not merely a diagonal surrogate.

D. Graph-domain identity and bounded inverse Neumann argument; two-sided Schatten ideal closure.

E. Independent axiom audit on the exact CI commit (no `sorryAx`, `Lean.ofReduceBool`), and no claim of a full theorem until A–D pass.

No floating-point quantity is needed for A. No 3,600,000-bit Arb claim is appropriate for exact integer arithmetic. No Lean compilation or CI is asserted by this audit.
