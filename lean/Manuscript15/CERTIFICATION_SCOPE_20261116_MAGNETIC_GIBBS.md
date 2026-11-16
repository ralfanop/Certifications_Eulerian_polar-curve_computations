# M15 — Magnetic Gibbs Transport (16 November 2026)
Authoritative archive: Manuscript_15_Magnetic_Gibbs_Transport_20261116(1).zip
SHA-256 7b2476cb99b68fe7322efbd3d4eb14ea8eb35019399d6eba13745094fa3cfc41
Library libfile_5d0f91134afc8191ac11943c568ed372.

Direct diff of 15.tex against Lipschitz Extensions identifies a new 395-line geometric/transport block and the 76-line §8.4, plus bibliography and notation changes. Preserve all prior obligations (#323, #325, #327, #329, #334, #335); this is not a replacement of existing certificates. No manuscript/figure files changed.

| LaTeX label | New candidate Lean work | Outstanding requirements |
|---|---|---|
| prop:arcsine-qc | exact rational Schwarzian and dilatation bound | actual holomorphic branch, derivative and norm estimates, affine Schwarzian transformation, Ahlfors–Weill extension |
| cor:cusp-ahlfors | previous cusp bridges in #335 | actual asymptotic and smaller subarc argument; Ahlfors necessary condition |
| prop:uniform-arcsine-transport | algebraic relation W1/W2, arithmetic difference and rational Jacobian constants | actual law construction, CDF and coupling optimality for p=1,2,infinity; integrals, monotonicity, maximum, scaling; principal Dirichlet Euler products and Möbius inverse; real Monge–Ampère determinant |
| prop:hamiltonian-euler | no complete theorem yet | actual Hamiltonian flow, symplectic preservation, pushforwards, differentiability under integral, iterated Euler operator |
| prop:arcsine-kahler | exact boundary rational coefficients | actual mixed derivative, sharp open-disc bounds and pullback identity (complex dimension one only) |
| thm:magnetic-wasserstein | all-integer odd lattice nearest-cell lemma, bounded and endpoint displacement, monotone scalar costs; actual primal infimum conditional on a.e. comparisons and attaining coupling; geometric normalization and partition sum | construct actual exponential and odd geometric laws, measurable rounding map and prove pushforward/coupling, compute cell integrals and essential supremum, construct magnetic Friedrichs operator and compact resolvent, verify Raymond hypotheses, min-max and diamagnetic heat-trace inequality, uniform trace and moment tails, weak + moments to Wp, reverse triangle inequality. **Fixed-index expansion is not by itself sufficient.** No W-infinity convergence claimed for original magnetic laws. |
| cor:mag-gibbs-special | partition normalization and algebraic variance/W2 identities | actual first and second moments via differentiated summable series, Eulerian identification and exact distances |

## Numerical scope
The scripts implement separate jobs for the new magnetic formulas and the earlier uniform–arcsine/arithmetic values. Each nonzero appropriate scalar individually asserts >=3,400,000 relative bits with 3,600,000 working precision, and proves the strict 1,000,001-significant-digit rounding cell via exact rational endpoints. They also test the nine published 50-place approximations against strict 50-place rounding cells. Exact endpoints, arbitrarily long decimal digits and balls are exported. Exact integers and rationals have exact derivations instead of fictional relative accuracy. Parameter-dependent expressions (all x, p, h and D) are analytic rather than finite numeric obligations. The geometric and magnetic laws are distinct; W-infinity = 1 for the limiting magnetic laws is an exact analytic statement, pending measure construction, not a numerical result. The workflow verifies the exact HEAD and audits all new Lean declarations against the standard foundational axiom whitelist. Candidate status until CI succeeds on that HEAD.

No merge, source/figure regeneration, or modification of M11–14, V007 or V097.
