# Manuscript 16 v16.4, Section 13: graph-domain Schur factor — analytic proof obligation

Status: **mathematical proof note, not a Lean certificate**. No FLINT/Arb claim. Do not merge automatically.

Source of truth: `Manoscritto_16_4_Editorial_Abstract200_Sezioni14-16_20261114(1).zip`, Library ID `libfile_cf2f1684406881919b233e666d54445b`, ZIP SHA-256 `c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f`. Only Section 13, equation `mixed-factor-164` and theorem `dirac-maxwell-obstruction-164`, are in scope. The authoritative source is unchanged.

## Precise setting

Let `X,P` be complex Hilbert spaces. Let `D = Dom(L0)` with graph norm `||x||_D = ||x||_X + ||L0 x||_X`. Assume `L0:D -> X` is closed, bijective, with bounded inverse `R0:X -> D` (in particular `||R0||_(X->X)=2/3` in the manuscript). Let `E:X->X` be bounded, `||E||<3/2`, and `L=L0+E:D->X`. Let `B:X->P`, `C:P->X` be bounded.

The resolvent identity, valid on X, is
`L^{-1}=R0 (I+E R0)^{-1}`, and hence `||L^{-1}||_(X->X) <= 1/(3/2-||E||)`.
Its range lies in D. For `y in X`, set `x=L^{-1}y`. Since `L0 x = y-E x`,
`||x||_D <= ||y|| + (1+||E||)||x|| <= [1+(1+||E||)/(3/2-||E||)] ||y||`.

Thus, for every `p in P`,
`||L^{-1} C p||_D <= [1+(1+||E||)/(3/2-||E||)] ||C|| ||p||`.

## Triangular isomorphism on the actual graph domain

Define `T:P ⊕ D -> P ⊕ D` by `T(p,x)=(p,x+L^{-1}Cp)`.
Then `T^{-1}(p,x)=(p,x-L^{-1}Cp)`, and both maps are bounded for the product of the P norm and the graph norm on D. This is the *right* factor in `mixed-factor-164`.

Define `S:P ⊕ X -> P ⊕ X` by `S(p,y)=(p+B L^{-1}y,y)`. Its inverse is `S^{-1}(p,y)=(p-B L^{-1}y,y)`; these are bounded on the codomain product norm.

For `F=A_P-BL^{-1}C`, direct evaluation yields, for `(p,x) in P ⊕ D`:
`S (F ⊕ L) T (p,x)=(A_P p+B x,Cp+Lx)`.
This is an equality of bounded maps `P ⊕ D -> P ⊕ X` once D is endowed with the graph norm. Crucially, it is **not** an equality of bounded endomorphisms of `P ⊕ X` when L is unbounded.

## Remaining Lean 4 tasks (not yet certified)

1. Construct the graph-norm Banach space D, with its inclusion into X and bounded realization `L0:D -> X`; prove completeness from closedness of L0.
2. Realize `L^{-1}:X -> D` as a bounded linear map, using the estimate above, not merely as an X-valued bounded inverse.
3. Implement `T,T^{-1}` as continuous linear equivalences on `P ⊕ D`; implement `S,S^{-1}` separately on `P ⊕ X`.
4. Formalize the factorization as equality between the *two distinct* spaces; then use invariance of kernel, cokernel and index under these equivalences.
5. Only subsequently use compactness of `BL^{-1}C` and Atkinson to transfer Fredholmness from F to `A_P`. The `det_4` criterion requires an additional Schatten ideal and regularized determinant bridge.

**Certification ledger:** exact algebraic identities: mathematical derivation in this note; Lean proof: OPEN; axiomatic audit: OPEN; CI: OPEN; Arb: NOT APPLICABLE; full operator Fredholm theorem: OPEN; determinant criterion: OPEN. Do not promote this note to certified status without a successful HEAD-pinned Lean workflow and explicit axiom audit.
