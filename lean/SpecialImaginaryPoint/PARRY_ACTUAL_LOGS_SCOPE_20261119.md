# M14 — actual Parry logarithm estimates, 2026-11-19

Authoritative source: Manuscript_14_Dominant_Pole_Preliminaries_20261117 (1).zip,
SHA256 b8285caa19e3ad809951b570f1f02abcfbfef845992681195f9283631b262171.
Proposition label prop:parry-index, equation label eq:parry-index-asymptotics
(225). No manuscript or figure changes.

This increment builds on #362 and #371, rather than replacing those results.
It addresses the actual denominator lower bound, actual beta positivity,
logarithmic scale and finite Taylor remainders of both actual logarithms
with t=x², plus approximation of the true Taylor arguments by sinh25.
These are proposed Lean theorems pending exact-head workflow success.

Remaining: uniform polynomial composition/truncation linking logPoly applied
to the polynomial arguments with A12 and C12 of #371, then unconditional
application of parry_expansion_transfer and conversion to O(x^22 log(1/x)).
No claim that these remaining obligations have been proved.
No numeric quantities are introduced; all error-bound coefficients are exact
rationals or integers. The existing Arb certificates are preserved.
