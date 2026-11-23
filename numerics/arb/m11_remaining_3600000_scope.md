# Manuscript 11 — remaining exact 20,000 fractional-decimal obligations (23 November 2026)

**Source:** author-owned Manuscript 11, Eq. (50) for the curvature discrepancy.
**Scope:** only the two remaining quantities; no changes to LaTeX, figures, Lean 4 modules, or certificates for other manuscripts.

## Definitions

1. Full Eulerian arclength L_E = integral[-pi,pi] sqrt(r_E(t)^2 + r_E'(t)^2) dt,
   r_E(t) = sin(t/2)/(t/2), with the analytic value at zero. The printed
   5.5510... is only a prefix (rounding to four places would give 5.5511).
2. D_kappa = sqrt(I_left + I_right), the two independently validated integrals
   for the normalized-arclength curvature discrepancy in Eq. (50).
   Printed 24 fractional digits: 0.203783759536049443826081.
   This excludes the corner atom, not the periodically closed-curve distance.

## Verified historical full numerical CIs

- [Length, run 44359739062](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44359739062):
  32 rigorous Cauchy Taylor panels and exact dyadic recombination,
  **100,031 actual relative bits**; successful for the original source SHA.
- [Curvature, run 44341455510](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44341455510):
  two independently bounded half-integrals, **25,503 actual relative bits**.
- Run 44518274867 was a **single** 200k-bit blocked panel using approximately
  12 GB and over 30 minutes; not a complete-length certificate.

## Current acceptance standard — exactly 20,000 fractional places

For EACH complete numerical quantity, return an Arb interval with rigorously
outward rational endpoints, sufficient working precision (typically >=80,000
bits), and enough actual relative accuracy to support 20,000 digits after
the decimal point (the auditor has an additional >=66,439-relative-bit gate).

**Decisive requirement:** every exact endpoint must lie STRICTLY inside
the SAME exact nearest-even rounding cell of width 10^(-20000). A statement
about relative bits alone is not enough. Verify the printed curvature
24-decimal cell independently. Save the resulting 20,000-place strings and
their SHA-256 digests as auditable CI artifacts.

The auditor `m11_remaining_3600000_final_audit.py` now:
- recomposes all 32+ independently generated length panel rational intervals,
  requiring every panel exactly once, with consistent numerical parameters;
- recomposes both curvature half-integrals EXACTLY, checking that the reported
  D_kappa interval encloses the square root of their interval sum;
- verifies exact decimal rounding cells and an independent Arb accuracy gate,
  rejects incomplete or mismatched data, and emits the full decimals plus hashes;
- requires a source HEAD SHA tag on both complete manifests. Tags alone are
  **not** proof of origin: CI must pin the checkout and independently verify
  the source of the numerical manifests.

The earlier length 100,031-bit result is *potentially* sufficient for the
20,000-place cell test, but it is **not yet accepted** as a new-HEAD certificate:
its historical source SHA and original panel artifacts require trustworthy
retrieval and provenance checks. A manifest must not be relabeled as the
current HEAD without recomputation or verified provenance.

## Computational strategy, informed by seven supplied papers

- **Length:** avoid repeating 150k full-panel pilots merely to prove an easier
  20k-place claim. Test the existing historical complete rational intervals
  and their 32 source panels; if not accessible/verifiable, produce fresh
  Cauchy/Petras certificates at a sufficient but bounded precision.
- **Curvature:** use independently certified local inverse-ODE radii and
  Taylor continuation. Investigate adaptive Taylor order and step selection
  (Arioli 2026; Jorba–Zou 2005), rigorous remainder majorants (Mezzarobba 2019),
  and memory-bounded evaluation (Mezzarobba, Space Complexity).
  Petras/Gauss–Legendre is viable for the final integration ONLY after a
  rigorous complex-analytic extension of the inverse ODE is established
  (Johansson 2018; Johansson–Mezzarobba 2018).
- Formal verification of Taylor-model specifications may use Park–Thies
  (2024) as an architectural reference, not an existing Lean 4 proof.

The old file names containing `3600000` remain solely for historical
traceability; they do not define the current target.

## Open proof/computation obligations

1. Revalidate the historical complete-length certificate against exactly
   20,000 decimal cells, with honest HEAD/source provenance and full panel data.
2. Raise the full two-sided curvature enclosure from 25,503 to a level
   sufficient for 20,000 exact decimal cells (with guard bits).
3. Run the complete auditor on pinned source inputs, publish the two entire
   certified strings and all rational interval/provenance artifacts.

**Status:** no final 20,000-place completion claim yet. CI syntax or synthetic
unit-test success is not numerical certification. **No merge.**
