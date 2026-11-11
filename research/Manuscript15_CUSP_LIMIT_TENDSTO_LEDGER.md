# Manuscript 15 — Actual punctured cusp quotient limit

This PR targets Proposition 5.1 (label `prop:cusp`) in the source
manuscript. Unlike the earlier algebraic `cusp_leading_coefficient`
theorem of PR #112, the new theorem is a true `Filter.Tendsto`
limit of the **actual coordinate ratio** defined in the manuscript.

The proof separates:
1. An exact rational identity for X_f(t)^2/Y_f(t)^3 at t≠0,
   a≠0, f(t)≠0.
2. The second-moment input
   `(1-f(2t))/t² → 2σ²` on the punctured neighbourhood.
3. The normalization input `f(t)→1`.
4. Eventual nonvanishing of f(t).
5. Algebra of limits giving `32σ⁴/a`.

**Important remaining obligation:** derive hypothesis 2 rigorously
from a symmetric Borel probability measure with finite variance σ²,
using differentiation under integral and the characteristic function.
Hypothesis 3 follows from the same probability model's continuity and
normalization. Until these are formalised and connected, the result is
a conditional analytical bridge, not the full measure-theoretic
Proposition 5.1.

Candidate pending successful exact-head Lean CI with standard axioms.
No merge and no changes to the prior manuscripts.
