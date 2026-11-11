# Manuscript 15 — exact derivative of inherited Eulerian sinc at terminal roots

The original FourierModes real Eulerian kernel is
`r_E(t)=sinc(t/2)`; this source is reused directly.

A previously certified Manuscript 11 module
`EulerianCert.Corner` defines the equivalent quotient
`2 sin(t/2)/t` for `t≠0`, and provides its derivative. This
new bridge proves the exact **local equivalence** and derivative,
not merely a numerical finite-difference approximation.

Candidate Lean statements:
1. `FourierModes.rE t=Corner.rE t` for any t≠0.
2. `HasDerivAt FourierModes.rE (Corner.rE' t) t` for any t≠0.
3. `r_E'(2π)=-1/(2π)`.
4. `r_E'(4π)=+1/(4π)`.
5–6. The associated `HasDerivAt` facts for the genuine FourierModes kernel.

Once CI succeeds these supply the missing nonzero-root
differentiability hypothesis for the terminal endpoint jet formalization
(PR #203). The full convolution theorem additionally requires their
composition with g(t)=r_E(2t) and the M=1 case.

**Status:** candidate until successful exact-head kernel CI; no merge.
Manuscripts 11–14 and other branches remain unchanged.
