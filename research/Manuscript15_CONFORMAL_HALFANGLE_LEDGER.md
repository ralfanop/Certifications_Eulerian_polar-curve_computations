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
