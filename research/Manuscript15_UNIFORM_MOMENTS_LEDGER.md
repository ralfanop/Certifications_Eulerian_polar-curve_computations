# Manuscript 15 — Exact moments of centred-uniform law

This module contains actual interval integrals over the real interval
[-1/2,1/2], not merely algebraic substitutions of their known values.
Seven Lean 4 candidate proofs:

- Total Lebesgue mass 1, centred mean integral 0.
- Even raw moments of orders 2, 4 and 6 are 1/12, 1/80 and 1/448.
- Third raw moment is 0.
- The fourth cumulant is exactly -1/120.

The exact integral identities support the analytic rigidity,
finite-variance cusp, fourth-moment cusp and convolution calculations.
The fourth-moment convolution arithmetic was separately kernel-certified
in PR #188; those arithmetic results do not establish independence
or the actual convolution law.

**Remaining:** instantiate the *probability measure* as the
normalized restriction of Lebesgue measure, transfer these
interval-integral values to its expectation and construct independent
convolution families. This is not accomplished by exact integrals alone.

Status: candidate until successful CI for the exact source head.
Prior Manuscripts 11–14 and Arb numerical certificates unchanged; no merge.


## Successful exact-source CI

[GitHub Actions #43190704554](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43190704554) completed **SUCCESS** with executable-source commit `9a2132b9733ac77d5ba58a5045240e3572b9e045`. Seven exact uniform Lebesgue interval-integral and fourth-cumulant declarations passed the kernel; actual probability-law integration is addressed by the stacked PR #242. Its pinned workflow checked the declarations and rejected forbidden axioms. This entry does not assert completion of the remaining source manuscript theorems; future executable changes must be rechecked.
