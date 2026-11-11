# Manuscript 15 — fourth-moment and convolution arithmetic

This new Lean 4 module covers only the **exact rational/algebraic subclaims**
needed for the higher-order cusp quotient, not their analytic or probabilistic proofs.

- The centred-uniform fourth-moment polynomial agrees with
  M/80 + 6 (M(M−1)/2)(1/12)² = (5M²−2M)/240.
- Substituting variance M/12 into 32 σ⁴/a gives 2M²/(9a).
- Substituting the fourth-moment polynomial into
  3 σ² − 2 m4/(3σ²) gives (5M+4)/60 for M≠0.
- The fourth moment is recovered algebraically from the quadratic
  coefficient b: m4=(3σ²/2)(3σ²−b) when σ²≠0.

**Pending** until exact-head kernel CI succeeds: four Lean declarations in
`lean/Manuscript15/HigherCuspArithmetic.lean`.

**Still unformalized:** measure moments of convolution sums, smooth
Taylor expansion with certified remainders, asymptotic cusp quotient,
terminal derivatives and curvature behavior. Do not treat these Lean
identities as proofs of those larger propositions.

Changes are isolated from Manuscripts 11–14, V007 and V097. No merge.
