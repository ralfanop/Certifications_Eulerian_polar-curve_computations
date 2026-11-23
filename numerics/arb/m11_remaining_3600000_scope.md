# Manuscript 11: remaining 3,600,000-bit Arb obligations (23 November 2026)

**Source:** author-owned `Manuscript_11_20261123_Eq33_24decimali.zip`;
source label `eq:Dkappa`, present Eq. (50).
This record alters **no manuscript text, figures, LaTeX or existing certificate**.

## Quantities and exact definitions

1. Full Eulerian polar-curve length:
   `L_E = integral[-pi,pi] sqrt(r_E(t)^2 + r_E'(t)^2) dt`,
   `r_E(t)=sin(t/2)/(t/2)` with the analytic value at zero.
   The printed `5.5510...` is a **prefix**, not a
   correctly rounded four-decimal value (`5.5511`).
2. Curvature discrepancy `D_kappa`, the square root of the
   normalized-arclength integral on the two independently
   parametrized smooth arcs (Eq. (50) in this frozen source).
   The printed `0.203783759536049443826081` has 24 fractional digits.
   It excludes the corner atom and is **not** the curvature
   distance of periodically closed curves.

## Verified prior CIs — NOT the final bit target

| Job | Exact source | Result |
| --- | --- | --- |
| [44359739062](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44359739062) | 32 individually rigorous Eulerian panels, recombined from exact dyadic endpoints | **100031** actual relative bits, SUCCESS |
| [44341455510](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44341455510) | Two-sided, local-radius normalized-arclength curvature, exact dyadic endpoint recombination | **25503** actual relative bits, SUCCESS |
| [44518274867](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44518274867) | 200000-bit single blocked Eulerian panel, scaling benchmark | 12 GB / >30 min on a **single** panel, SUCCESS; not a full length certificate |

The existing `m11_euler_cauchy.analytic_disk` rigorously excludes
zeros of the complex speed square in the radius-five disk and supplies
the analytic Cauchy remainder; `m11_euler_panel.py` uses outward
Arb coefficients, per-panel Cauchy tails, and exact dyadic recombination.
The curvature code `m11_dk_adaptive_radius.py` uses independently
certified inverse radii, positive interval inequalities, and two-sided
phase continuation. Rely on their *actual* execution, not a floating
point approximation or overlap alone.

## Exact final acceptance standard

A new production run must produce the **entire** length (not one
panel) and the **entire** curvature discrepancy (not one half) with:

- `python-flint==0.9.0`, exactly `ctx.prec=3600000`
  working bits throughout the mandatory precision audit.
- `rel_accuracy_bits() >= 3400000` **for each final interval**.
- Strict containment of the two interval endpoints within the **same**
  correctly rounded **1,000,001-significant-digit decimal cell**,
  using exact rational endpoint comparisons.
- Independently checked Eq. (50) 24-decimal correctly rounded cell,
  and the `L_E` published prefix interval.
- Exact GitHub HEAD SHA, pinned source scripts, input manifest hashes,
  CI logs, outward endpoint objects, and compressed rounded digits.

The new `m11_remaining_3600000_final_audit.py` implements those
**fail-closed output checks**, but does not manufacture its required
3.6M-bit input enclosures. DO NOT run it on pilot files and never call
the final result SUCCESS before it passes on actual complete manifests.

## Scaling work started in this PR

The independent `m11-remaining-3600000-scaling.yml` first raises
the full Eulerian length to **150000 relative bits** (32 panels),
and full two-sided curvature to **30000 relative bits**.
It is a strictly lower-precision **scaling gate**, with separate CI
artifact names and no false `MILLION SUCCESS` text.
If resource limits prevent completion, inspect real logs and revise
the algorithm/chunking rather than weakening any mathematical assertion.

The eventual 3.6M-bit production jobs must be enabled only after
resource-scalable batching/checkpointing is demonstrated.
**Pending as of filing**: neither final 3.6M-bit enclosure exists.

No new Lean 4 theorem is required merely to print a longer numerical
approximation, assuming the exact identities and curvature analytic
bounds themselves are unchanged. This note does not equate numerical
Arb certification with complete Lean formalization of the integration
and nonvanishing arguments.

**No merge.**
