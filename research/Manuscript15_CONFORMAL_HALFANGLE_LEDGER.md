# Manuscript 15 — conformal half-angle real chart

Proposition **Half-angle formula in a Minkowski chart** contains the real
formula `Ω(q)=2 arctan(q)` and distinguished values at `q=1/2` and
`q=1/π`. This is an independent, deliberately narrow proof module:
- `tan(Ω(q)/2)=q` for every real q;
- zero and oddness of Ω;
- `Ω(1/2)/(2π)=arctan(1/2)/π`;
- `Ω(1/π)=EulerianCert.Corner.varthetaE`, referring to the actual
  inherited Manuscript 11 corner-angle definition.

**Not yet formalized:** the null-cone representative, projective chart,
complex Cayley identity `e^{iτ}=(1+iq)/(1-iq)`, principal-branch
condition `−π<τ<π`, or the two-sided conformal boundary limit.
These remain necessary for a full formal proof of the proposition.

All five declarations are **candidates** until successful exact-head
Lean 4 kernel and standard-axiom CI. No merges authorized. The earlier
manuscripts, vector figures and Arb certificates are not modified.


## Exact-source CI success (verified)

[GitHub Actions run #43178858951](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43178858951) completed **SUCCESS** for executable source commit `ae7ebe5fa5a108070aafcd729b9a52bffd108148`. Five exact real conformal half-angle identities kernel-checked. The projective complex-Cayley chart is not yet included. The workflow explicitly checks the Lean kernel and audits for `sorryAx` and `Lean.ofReduceBool` (or, for the full Eulerian table, asserts outward interval accuracy).

This is a historical immutable-source verification record. A documentation-only later commit does not change the executable source; any subsequent executable revision must be checked on its own exact commit before certification is transferred.
