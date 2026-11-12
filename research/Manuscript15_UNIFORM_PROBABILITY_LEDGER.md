# Manuscript 15 — Actual centred-uniform probability law in Mathlib

This module is a bridge from exact interval integrals and
characteristic-function identities to a genuine normalized Borel measure.

Definitions:
- `unitCentredInterval=Icc (-1/2) (1/2)`;
- `centredUniformLaw=ProbabilityTheory.cond volume unitCentredInterval`.

Proposed Lean declarations:
1. `volume unitCentredInterval = 1` (real Lebesgue volume).
2. `IsProbabilityMeasure centredUniformLaw` as a typeclass proposition.
3. `MeasureTheory.pdf.IsUniform id unitCentredInterval centredUniformLaw volume`.
4. `centredUniformLaw unitCentredInterval=1`.

These are **measure-level statements**, unlike the conditional algebraic
symbolic recurrence or elementary interval-integral identities.

This does not yet relate the complex characteristic function, prove
moment integrability for the measure, or prove the uniqueness theorem.
The needed analytic identities have been independently verified in
PRs #209 (real cosine/sine integral) and #233 (moment integrals).
The next formal step is to import both source modules and translate
their interval integrals into expectations under this probability law.

Status: CANDIDATE until CI succeeds on the exact executable source.
No earlier manuscript is altered; no merge is performed.
