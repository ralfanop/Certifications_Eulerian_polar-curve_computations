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


## Exact-source CI success (verified)

[GitHub Actions run #43177587227](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43177587227) completed **SUCCESS** for executable source commit `1936d3c33954082841d27a3038e9395efc92618c`. Six nonzero-root Eulerian kernel derivative and compatibility declarations kernel-checked. The workflow explicitly checks the Lean kernel and audits for `sorryAx` and `Lean.ofReduceBool` (or, for the full Eulerian table, asserts outward interval accuracy).

This is a historical immutable-source verification record. A documentation-only later commit does not change the executable source; any subsequent executable revision must be checked on its own exact commit before certification is transferred.
