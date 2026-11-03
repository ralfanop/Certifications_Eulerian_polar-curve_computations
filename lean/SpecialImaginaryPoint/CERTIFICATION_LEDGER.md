# Special point i/sqrt(2) — certification ledger (Draft 0.10r1)

This branch is intentionally independent of manuscripts 11, 12 and 13, the
existing PR #16, and the approved V097. Do not merge without the author's
separate approval.

Source: `Eulerian_i_sqrt2_Draft10r1.tex`. Each proof must match the **entire
printed statement**, not merely a finite-dimensional surrogate or a scalar
instance.

Legend: **pending** = not yet shown to be kernel-certified on this branch;
**partial** = the file proves only explicitly listed subclaims; **Arb** =
rigorous *scalar enclosure* from python-flint, NOT a proof of analytic identity.

| Printed result | Formalization status | Next Lean obligation |
|---|---|---|
| Proposition 2.1 Exact special-value chain | pending; classical special-function identities | Complex sin at imaginary argument; spherical/modified Bessel and 0F1 equality |
| Corollary 2.3 Explicit rational bounds | partial: integer denominator recurrence | Finite sums, positivity, exact infinite-series remainder enclosure |
| Proposition 3.1 Binomial input and beta integral | pending | Central-binomial generating function and beta moments |
| Theorem 3.3 Exact Borel–Eulerian specialisation | pending | Double-Borel coefficient map; analytic convergence and entire equality |
| Theorem 3.5 Differential-operator identity | pending | Coefficientwise formal-power-series identity with theta |
| Corollary 3.6 Eulerian second-order generator | pending | Pull-back by t=-z²/16 and differential equation |
| Proposition 3.7 Modified-Bessel beta average | pending | Beta integral, I0 expansion, exchange |
| Proposition 4.1 Two spherical realisations | pending; V007 sphere-marginal background available | Concrete area measure and I0 spherical integrals |
| Theorem 4.3 Cylindrical–spherical transmutation | pending | Equality on explicit differentiable domain |
| Proposition 4.4 Regular modified-Helmholtz profile | pending | C² radial equation, origin, uniqueness |
| Proposition 5.1 Special partition function and magnetisation | pending; Arb scalar enclosures | Integral, first and second log derivatives |
| Theorem 6.2 Complete domain-level commutation | pending; PR #16 Sturm work is NOT this theorem | Integral commutant, selfadjoint realization, exact domain |
| Corollary 6.3 Matching Fock parameter | pending | Scalar normalization with positive inputs |
| Proposition 6.4 Second-order Gegenbauer–Fock transport | pending | Exact differential intertwiner and analytic domain |
| Theorem 7.2 Statistical–spectral determinant | pending | Dirichlet eigenvalues, trace-class inverse, Fredholm product |
| Theorem 7.3 Langevin resolvent trace | pending; Arb scalar enclosure | Trace sum equals coth formula |
| Corollary 7.4 Hilbert–Schmidt trace | pending | Positive operator, HS trace and exact series |
| Proposition 7.5 Even-zeta expansion | pending | Log product and absolutely convergent series |
| Proposition 8.1 Hall–Bargmann evaluation | pending | Concrete transform and Gaussian cancellations |
| Proposition 9.1 Quadratic L-value normalization | pending | Quadratic L special values, discriminant −8 |
| Proposition 9.2 Class-number-one singular modulus | pending | CM j(i/sqrt2)=8000, correct modular normalization |
| Proposition 10.1 Hepner chiral scalar factor | pending | Gamma-matrix conventions and exact algebraic identity |

## Newly deposited modules

- `lean/SpecialImaginaryPoint/DenominatorRecurrence.lean` — universal
  recurrence `d(n+1)=8(2n+2)(2n+3)d(n)`, initial value, positivity
  and first five exact values. It has a dedicated `#print axioms` audit.
  Status becomes **kernel-certified only after SUCCESS** on the corresponding
  source SHA.
- `numerics/arb/special_point_i_sqrt2_arb.py` — 256-bit interval checks
  of four printed scalar quantities, exact rational remainder, and pi/sqrt8.
  The results are rigorously enclosed when its CI job concludes SUCCESS.
- Workflow `.github/workflows/special-point-i-sqrt2.yml` is strictly
  scoped to this branch.

## Non-transfer principle

A successful module of manuscript 13/V007 certifies only its actual Lean
statement, not a similar theorem of the present article. Existing proof
modules are evidence to reuse, not licenses to mark this ledger as completed.
Do not label any part "Lean certified" without matching SHA, successful
kernel compilation, `#print axioms` and audit of forbidden axioms.
