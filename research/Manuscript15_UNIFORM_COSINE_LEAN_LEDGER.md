# Manuscript 15 — Elementary uniform characteristic integral

This branch begins closing the largest gap in the rigidity theorem:
the identification of the characteristic function of the centred
uniform law with the **actual** inherited Eulerian sinc kernel.

It proposes to kernel-check three declarations:
1. Exact `t ∫_{−1/2}^{1/2} cos(tx) dx = 2 sin(t/2)`,
   valid for all real t including t=0.
2. Thus `∫_{−1/2}^{1/2} cos(tx) dx = r_E(t)`,
   where r_E is the inherited `EulerianCert.FourierModes.rE`.
3. The corresponding symmetric sine interval integral is exactly zero.

These are genuine interval-integral statements, proved using pinned
Mathlib integration theorems, not approximate numerical evaluations.

**Remaining probabilistic obligations:** package the interval uniform
law as a normalized Borel probability measure, express the complex
characteristic function as this cosine/sine pair, derive its
entireness and the Taylor coefficient recurrence, and invoke
characteristic-function uniqueness for the converse rigidity proof.

**Status:** candidate until exact-head Lean CI succeeds; no merge.
This branch does not alter Manuscripts 11–14, prior Lean
certifications or the numerical Arb parameter.
