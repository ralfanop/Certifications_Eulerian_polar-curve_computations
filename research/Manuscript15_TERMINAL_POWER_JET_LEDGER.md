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


## Successful exact-source CI

[GitHub Actions #43190410497](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43190410497) completed **SUCCESS** with executable-source commit `6ccdbccfc7da0f1cf85451cf43958efe010c1935`. All three universal zero-power jet derivatives are kernel-checked; their composition with the actual Eulerian kernel is documented in PR #236. Its pinned workflow checked the declarations and rejected forbidden axioms. This entry does not assert completion of the remaining source manuscript theorems; future executable changes must be rechecked.
