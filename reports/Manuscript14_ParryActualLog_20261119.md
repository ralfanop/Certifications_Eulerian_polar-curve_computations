# M14.119 equation (225) — actual logarithm remainder bridge

Frozen source ZIP: Manuscript_14_Dominant_Pole_Preliminaries_20261117 (1).zip
SHA256 b8285caa19e3ad809951b570f1f02abcfbfef845992681195f9283631b262171, as verified in lean/SharedCore/FROZEN_M14_M15_CERTIFICATE_RECONCILIATION_20261118.md.

Integrated prerequisites: #362 (actual Taylor theorem), #371 (exact residuals and transfer), earlier quantitative epsilon positivity.
New candidate: real beta(x)=sinh(x)/x > 1; log(beta(x))/x² >= 1/12 on 0<x<=1; actual logarithmic composition errors <=2(x²)^12; log(6/x²)>=1. The final reduction assumes only two finite composition truncation estimates, not positivity or additional analytic-log estimates. Exact-head CI required.

Remaining: replace actual epsilon arguments by their certified hyperbolic Taylor polynomials, prove the finite composition degree-12 and degree-11 rational coefficient truncation bounds, finish the unconditional remainder O(x^22 log(1/x)). No new Arb claims: coefficients and special evaluations already checked in #356–357. No manuscript/figure changes, no merge.
