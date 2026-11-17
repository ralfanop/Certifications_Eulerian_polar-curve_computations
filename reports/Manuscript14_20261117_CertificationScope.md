# Manuscript 14.119 — 17 November 2026, 71-page revision

Source: `Manuscript_14_Parry_x20_20261117.zip`, main file `14/14.119.tex`.
The terminal term of (201) is in x^20, with O(x^22 log(1/x)); the logarithmic
scale is J = log(6/x²). The source has an independent exact-rational checker
which was executed locally (all coefficients and 80 decimal places at both
special points). Changes to layout, notation, bibliography and Figure 3 do
not introduce mathematical assertions.

## This increment (CI required)

- `V14119ParryX20`: 64 exact rational declarations, checking factorial basis,
  log recurrences, reciprocal and product convolutions through degree 11,
  the three new zeta/Bernoulli coefficients, and the terminal coefficient.
- `V14119ParryRemainderX20`: exact logarithmic quotient identity and
  propagation of assumed order-t^12 Taylor error bounds through division
  by t. These are not yet the analytic Taylor bounds for the actual functions.
- `V14119Permeability`: exact cancellation of 4π, scaled-measure equality
  conditional on the normalised measure and SI identity, dimensionless ratio.
- `manuscript14_parry_x20_arb3600000.py`: both special arguments, beta, J,
  actual Parry quotient, truncation and signed truncation error, direct
  zeta terms and exact rational counterparts, exact geometrical normalisation,
  comparison with the CODATA central decimal and uncertainty. It checks
  at least 3,400,000 relative bits and one million and one significant decimal
  digits for each nonzero certified enclosure. The measured physical
  permeability itself does not have that experimental accuracy.

## Existing coverage / remaining obligations

- Prop. 10.2: `V14119ParryIndexCertificate` handles greedy indices and
  rational threshold brackets. `V14119Asymptotic177Quotient` and its
  dependencies prove the old order-x² log(1/x) quantitative estimate.
  The new order-x^22 analytic remainder still requires proving the
  order-t^12 Taylor bounds for P=t/log B and R=-P log(6(B-1)/t), then
  applying the propagation lemma. Finite coefficients and two numerical
  samples do not prove those uniform bounds.
- §9: `BlochMeasureCertificate` contains the affine-coordinate pushforward,
  axial probability and spherical partition-function proofs. Its own scope
  notes the compactification/homeomorphism and Archimedean surface-measure
  identification remain separate. This increment adds the SI/measure scaling
  algebra, not an empirical determination of a physical constant.
- §7.4: existing `Section74MagneticHeat`, `Section74HeatMomentLimit`,
  `Section74LocalMagneticCoercivity`, `Section74ConfinementCutoff` cover
  spectral-series identities, moment limits, coercivity and abstract cutoffs.
  The concrete operator/PDE construction and diamagnetic comparison remain
  obligations, not assumptions silently counted as formalised results.
- Earlier sections: existing repository modules and their corresponding CI
  must be audited against the final source before claiming complete coverage.

No declaration or Arb job is counted as verified until its exact-head CI
passes. No merge in this increment.
