# M16 v16.4 §13 — finite cutoff, exact HEAD audit (2026-11-15)

Authoritative source: `Manoscritto_16_4_Editorial_Abstract200_Sezioni14-16_20261114(1).zip`, SHA-256 `c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f`.
Source statement: `prop:mixed-schatten-164`, equation `eq:mixed-lower-series-164`.

## Scope
Finite comparison of the Maxwell nearest-mode p=3 summands against shifted harmonic summands. Four scoped Lean declarations: rational identity, pointwise positivity, arbitrary finite-set sum comparison, and interval cutoff.

## CI failure and correction
PR #321, HEAD `7161ac829e1475079ed2ac25595a15c5a8a6cd6b`, run `43702962786` FAILURE. Actual Lean error: `unknown module prefix 'Manuscript16'` at line 5 of the finite-cutoff file. Prior workflow attempted to write a local `.olean` outside Lake's registered import search path.

This revision makes the proof **self-contained** under `import Mathlib`, deriving the pointwise bound from its exact rational gap; it removes the problematic local module import and tests all four #print axioms. Status remains **PENDING until the new exact-HEAD CI succeeds**.

## Certification boundary
No Arb work: these are exact rational/finite inequalities, not nonzero transcendental numerical quantities. Existing #318 Arb 3600000-bit scalar certificates are unaffected. The harmonic-series divergence, spectral trace identification, sharp operator Schatten threshold, Fredholm equivalence, and det4 invertibility theorem are separate analytic obligations. No complete operator theorem is claimed.
