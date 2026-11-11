# Manuscript 15 — Terminal jet differentiation of convolution powers

Theorem 7 / endpoint-derivative mechanism in the source manuscript:
the presence of a zero of the Eulerian kernel and powers M≥2 makes
the first coordinate's derivative nonzero, while the second coordinate's
derivative is zero for every M≥1.

New general Mathlib Lean declarations:
- `hasDerivAt_power_zero`: if g(x)=0 and g is differentiable at x,
  then `(g^M)'(x)=0` for M≥2;
- `hasDerivAt_power_reconstruction_X`:
  `(a t (1-g(t)^M))'(x)=a` for M≥2;
- `hasDerivAt_power_reconstruction_Y`:
  `(a t² g(t)^(2M)/2)'(x)=0` for M≥1.

These are universal local derivative identities at a zero and are not
specific to any probability distribution. To obtain the full source
convolution theorem, instantiate `g(t)=r_E(2t)` for X and
`g(t)=r_E(t)` for Y at t=2π, including local differentiability of
the inherited Eulerian sinc at each nonzero zero. M=1 for the X coordinate
must be handled separately using the exact cycloid identity.

**Status:** candidate pending successful exact-head kernel/axiom CI.
No analytic assumption is silently discarded; no merge.
