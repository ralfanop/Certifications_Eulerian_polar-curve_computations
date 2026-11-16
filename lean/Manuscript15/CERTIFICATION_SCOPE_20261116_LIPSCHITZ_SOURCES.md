# M15 — 16 November 2026: Lipschitz Sources, §8 and Figure 2

Authoritative archive: Manuscript_15_Lipschitz_Sources_20261116 (1).zip
SHA-256: 9b4f15263894f25d3d5ddc29f8cdb839c53e9fcf31115642ed967b4c75aab09b.
Library ID: libfile_50c404808e188191a8c82fba105ed52c.
Source reviewed: 15.tex and FIGURES/Figure_Omega_Lipschitz.tex.
This supersedes edited content only, retaining all earlier obligations (including #323, #325, #327, #329 and the Extended Maldacena revision). No figure or manuscript source changes.

| Label | Draft coverage | Outstanding |
|---|---|---|
| fig:omega-lipschitz | exact disk centre, radius, bottom point, positive imaginary coordinates 1/√2 and √2; scalar L₀=2/√5; exact-endpoint Arb audit | exact CM theorem j(z₀)=j(z₁)=8000 is not inferred from ball inclusion; independent numerical modular evaluations are separate |
| eq:cat-lipschitz-bound, eq:cat-lipschitz-constant | Lean candidate for sharp norm and reciprocal square-root bound, boundary equality | actual holomorphic arcsine derivative formula, complex segment integration and sharpness of Lipschitz quotient |
| eq:cat-bridge, eq:cat-factorial-special, eq:cat-scale, eq:cat-scale-t, eq:cat-vacuum-special, eq:cat-vacuum-lipschitz, eq:cat-angle-gd, eq:cat-lipschitz-gd | rigorous closed-form finite numeric checks, not proofs of equality from overlaps | analytic identities, actual L(1,χ₅) evaluation and vacuum/arcsine links |
| eq:cat-arcsine-moments, eq:cat-reconstruction-resolvent, eq:cat-resolvent-theta2, eq:cat-operator-differentiation | scalar rational rearrangement in Lean | Wallis integral, pushforward measure, bounded multiplication operator, norm limit and differentiation, jet recovery |
| eq:cat-graph-r4 | none yet | holomorphic embedding and uniqueness |
| eq:cat-special-z0, eq:cat-special-product, eq:cat-final-synthesis, eq:cat-chi-minus8 | high-precision finite closed-form scalars | Dirichlet integration and analytic equivalence |
| fig:omega-lipschitz numerical j=8000 | separate modular computation at both arguments | exact theorem not certified by approximation; imaginary part zero only an enclosure unless independently proved |

Figure's L₅(1,χ₁) notation corresponds to the text's positive discriminant-five character, subject to its convention. Plotting offsets, colours and font sizes are not mathematical constants.

Standard: 3,600,000 working bits, independently asserted >=3,400,000 relative bits, strict rounding cell for 1,000,001 significant digits from exact dyadic endpoints, retain endpoints and balls. Exact rationals recorded separately; no relative-bit claim for exact zero. All new results are candidates until exact-head workflow succeeds. No merge.
