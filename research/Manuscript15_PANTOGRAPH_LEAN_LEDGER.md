# Manuscript 15 — Pantograph antecedent formalisation

This follows precisely the source manuscript's remark identifying the
published Ozturk–Gulsu pantograph differential equation, without claiming
novelty for the antecedent.

Conditional on successful pinned CI, five Lean 4 statements:
1. Algebraic identity y(t/2)^2 = t^2 f(t)^2 /4 for y(t)=t f(2t).
2. HasDerivAt of the transformed function y at t when f has a derivative at 2t.
3. Exact passage from 1-f(2t)-2t f'(2t)=t^2 f(t)^2/2 to
   y'(t)=1-2 y(t/2)^2.
4. Pointwise reverse implication from the pantograph ODE to the f equation.
5. Sine is a solution of y'=1-2 y(t/2)^2.

**Limitations:** these are identities and pointwise derivative facts.
They do not prove uniqueness of the nonlinear pantograph Cauchy problem,
uniqueness of an entire characteristic function or uniqueness of a
compactly supported probability measure. Those remain tracked in the
Manuscript 15 full-coverage ledger.

Pinned Lean: v4.35.0-rc3, Mathlib 0272bbe1...; CI must pass on exact
source head and #print axioms must show only standard axioms. No merge.


## Exact-source CI success (verified)

[GitHub Actions run #43177583436](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43177583436) completed **SUCCESS** for executable source commit `893c0ef5395a9f5e6dd26cf2014c933bfcb63217`. Five derivative/substitution/sine-solution statements kernel-checked. Characteristic-function and pantograph uniqueness are not covered. The workflow explicitly checks the Lean kernel and audits for `sorryAx` and `Lean.ofReduceBool` (or, for the full Eulerian table, asserts outward interval accuracy).

This is a historical immutable-source verification record. A documentation-only later commit does not change the executable source; any subsequent executable revision must be checked on its own exact commit before certification is transferred.
