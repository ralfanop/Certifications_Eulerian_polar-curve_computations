# Manuscript 15 — §§9–12 formalisation register
Frozen editorial reference: Manuscript_15_20261125_EQ499_508_SEPARATE, 146 pages. Stable LaTeX labels, not earlier display numbers, are authoritative.

## Initial Lean candidate (26 statements, exact-HEAD CI required)
- §9 prop:ridge-metric: determinant, positivity, normal orthogonality and squared norm of the displayed tangent-frame vectors (5).
- §9 cor:ridge-crease: scalar zero criterion under positive scale, positive radius and nonnegative k (1).
- §9 eq:ridge-agnesi: self-dual orbit differential identity (1).
- §10 prop:ridge-maxwell: actual 3x3 determinant, both inverse products, scalar quadratic form, positivity, characteristic polynomial and golden-ratio reciprocal root identities (7).
- §10 prop:ridge-node-new: algebraic factorization (1).
- §10 prop:ridge-area-new: quartic difference, nonnegativity, primitive endpoint value, central squared height (4).
- §10 prop:ridge-error-test-new: conditional a posteriori scalar bound (1).
- §11 prop:grav-hyd-comparison: scalar consequences of the perimeter bound and deltoid formula, including strict real-power comparisons (5).
- §12 eq:cross-ridgePotential15: pointwise normalized potential identity in explicit scalar form (1).

## Existing coverage to reuse
PR #613 merged: CrossQuarticCurve20261125.lean, CrossQuarticFibreClassification20261125.lean, CrossQuarticPeriodDifferential20261125.lean and CrossQuarticFinitePeriod20261125.lean are present on main. Their precise theorem statements and axiom audits must be matched against §12 before closure.

## Open obligations (not proved by this PR)
§9: exact polar profile derivative and Fourier coefficients/asymptotics; centered aperture and acceptance; elliptic geodesic integral and analytic continuation; actual differentiated immersion, second fundamental form, curvatures and torsion, zero-curvature asymptotic.
§10: shape derivative of circular doublet; Dirichlet spectral stability and actual transverse eigenvalue bounds; reflection parity; Gaussian integral representation; flux-normalized scattering and recovery; physical graph/analytic-node distinction and analytic inverse function theorem; quartic Taylor error and integration; eigenspace convergence, Maxwell compactness, conditional scattering continuity, trapped modes and bounded-domain exclusion; dihedral formula, minima and Laplace localization; harmonic Dirichlet corrector and harmonic duality, scalar fractional asymptotic; conditional selectivity and extremal coefficient formulas; all remaining mathematical claims not mapped to a kernel declaration. Global fractional Maxwell response is a conjecture, not a proven theorem. Discrete numerical estimates and continuum error/threshold checks are distinct from Lean algebra.
§11: reflected isoperimetric result, actual Eulerian integral estimate using Cauchy–Schwarz and pointwise radial bounds, hypocycloid area and perimeter integrals, Manning equal-area reduction. Figure caption does not prove a specified isotopy; no relativistic transport or Einstein-matter theorem is claimed.
§12: cross-reference the already merged quartic modules; actual elliptic period identities, analytic/remainder and uniform limit, and vacuum-limit dependence on prior results remain to be checked. Scalar pointwise identity does not certify these dependencies.

No certification asserted before successful exact-head Lean CI, with ordinary kernel axioms only. No new numerical Arb run, no manuscript edit, no merge.
