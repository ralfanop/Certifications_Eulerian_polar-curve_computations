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


## Extended complete curvature propositions (pending exact-head CI)

The source now defines the actual unsigned curvature using the determinant of the velocity/acceleration and the cube of the speed, and proposes the two additional theorems `cycloid_curvature_exact` and `cycloid_curvature_radius`. They state exactly `κ(t)=1/(4a sin(t/2))` and `R(t)=4a sin(t/2)` on the regular arc `a>0, 0<t<2π`. This extension is **unverified until the new exact-head Lean CI completes**; the prior successful CI covers only the original four statements.


## Exact-source CI success (verified)

[GitHub Actions run #43190294217](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43190294217) completed **SUCCESS** for executable source commit `51b7fb95ad8fcd6f039c6f36a5e1d57df415ac9e`. Six exact cycloidal speed, curvature and radius statements kernel-checked, including the full unsigned regular-arc curvature. The workflow explicitly checks the Lean kernel and audits for `sorryAx` and `Lean.ofReduceBool` (or, for the full Eulerian table, asserts outward interval accuracy).

This is a historical immutable-source verification record. A documentation-only later commit does not change the executable source; any subsequent executable revision must be checked on its own exact commit before certification is transferred.
