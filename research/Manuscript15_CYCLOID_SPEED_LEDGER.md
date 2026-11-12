# Manuscript 15 — cycloid speed and signed curvature numerator

Targets the source **Proposition: Speed and curvature realisations**
after the already kernel-certified exact reconstruction in Manuscript 15.

Four Lean candidates:
1. `1−cos(t)=2 sin(t/2)^2` for all real t.
2. Exact squared-speed identity for all real a,t, including cusps.
3. Signed planar curvature determinant
   `X'Y''−Y'X''=a²(cos(t)−1)` for the cycloidal parameter.
4. True speed formula `sqrt(X'^2+Y'^2)=2a sin(t/2)`
   for `a>0,0<t<2π`.

Still necessary for the **full** proposition: formalize the
(nonzero) speed-cubed denominator of unsigned curvature, the radius
inverse and identification with the inherited Eulerian sinc.
No claim that the denominator reduction is already kernel-checked.

The work follows the source exactly, with no physical interpretation.
CI uses pinned Lean/Mathlib, prints all axioms and rejects forbidden
axioms. **Candidate until exact-head workflow SUCCESS**, no merge.
