# M15 — certification scope for Discussion-First, 15 November 2026

Authoritative supplied archive: `Manuscript_15_Discussion_First_20261115 (1).zip`.
SHA-256: `0c80a4bc28f99b20239d8640f9ed29d53640309998a05e92c24b0d0fe1ba3ec7`.
Read the LaTeX source and README; the mathematical results previously in Appendix B are now integrated in Sections 5–7. Discussion is §8, New research directions §9, Open Problems §10, Conclusions §11.

Historical results remain preserved and scoped to their respective declarations and source revisions. PR #318 covers 13 finite angles (n=3..15), not n=16,17. PR #309 covers the sharp characteristic-function estimate; #319–320 address metric properties. This revision must not treat those as certification of unrelated new statements.

| Source label / section | Present draft | Remaining obligation |
|---|---|---|
| Table 1 and Appendix A, n=16,17 | exact full rows, mass, symmetry, mean, variance, central slopes; two angles in radians/degrees at 3,600,000 working bits | all-order asymptotics, figure reproduction not claimed |
| thm:wasserstein, §7.4 | actual characteristic real-part profile and both pointwise coordinate inequalities from #309 | explicit symmetric-law identification and compact-uniform topology formulation |
| prop:cusp-sixth, thm:cusp-all-orders, thm:all-order-curvature | manuscript symbolic checks are historical algebra only | analytic differentiability, convergence, coefficient recurrence and triangular recovery in Lean |
| thm:terminal-all-order, §6.2 | leading and first correction closed scalar numerical examples M=2,3,4,5,8 | analytic local inverse, Lagrange–Bürmann coefficients and remainder for arbitrary M |
| prop:hopf-terminal, §6.3 | scalar factorization of leading coefficient, ball for 4π² | geometric Hopf-fibre isometry, spectral multiplicities, zeta continuation/determinant identification |
| prop:hopf-enumerative-surface, §6.4 | not claimed | compact graph and Mellin transform |
| prop:squarefree-eulerian-det, §6.5 | not claimed | squarefree zeta identity, zeta determinant, absolute double-product and log series |
| prop:terminal-reg-product, §6.5 | numerical scalar A^(-1/12), log(A)/12 and log(A) | analytic Laurent coefficient and generalised residue regularization |
| prop:hopf-thue-morse, §6.5 | exact scalar product, ratio and terminal coefficient algebra conditional on displayed sector formulas | actual Thue–Morse Dirichlet sectors and Flajolet–Martin constant, rigorous infinite-product/tail algorithm for individual sector values |
| thm:central-slope-all-order, §7.2 | not claimed | uniform remainder, Gaussian moments and asymptotic all orders |

CANDIDATE until exact-head CI succeeds. New numerical claims require every appropriate nonzero quantity to have an individually asserted relative accuracy ≥3,400,000 bits at fixed 3,600,000-bit working precision **and** strict 1,000,001-significant-digit rounding-cell inclusion using exact dyadic endpoints (shared #318 checker). Exact integers/rationals are recorded separately with arithmetic justification; no relative-bit claim for zero. No figure regeneration or changes to other manuscripts. No merge requested.
