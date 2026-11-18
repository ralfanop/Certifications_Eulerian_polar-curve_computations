# Frozen M14–M15 numerical certification reconciliation (2026-11-18)

Scope: metadata reconciliation only; this document does not certify any new quantity. Manuscript sources and figures remain frozen.

## Authoritative source archives (SHA-256 independently checked against raw Library ZIP bytes)

| Manuscript | Archive | SHA-256 | Status |
|---|---|---|---|
| M14 | Manuscript_14_Dominant_Pole_Preliminaries_20261117 (1).zip | b8285caa19e3ad809951b570f1f02abcfbfef845992681195f9283631b262171 | MATCH |
| M15 | Manuscript_15_Magnetic_Gibbs_Transport_20261116(5).zip | 7b2476cb99b68fe7322efbd3d4eb14ea8eb35019399d6eba13745094fa3cfc41 | MATCH |

M14 source: `14/14.119.tex` (338 LaTeX labels); M15 source: `15.tex` (383 labels). Older source ZIPs are superseded; their certification scopes are retained only after formula-by-formula reconciliation.

## Deduplicated quantity / LaTeX label / certificate / exact-head matrix

| Canonical quantity | Manuscript and final LaTeX label | Existing certificate provenance | Exact certified HEAD | Reconciliation outcome |
|---|---|---|---|---|
| A = ζ(2) − ζ(3) | M14/M15: exact formula/label mapping **not yet verified** | PR #377, three-value Arb job, 3,600,000-bit working precision, 1,000,001-digit strict rounding claimed in CI log | `3d1ecb565fe71a81ddf715b101ae2ca0a98b63e8` | CERTIFICATE EXISTS for shared diagonal test model; manuscript formula match PENDING |
| −A/4 | M14/M15: exact formula/label mapping **not yet verified** | Same PR #377 Arb job | `3d1ecb565fe71a81ddf715b101ae2ca0a98b63e8` | CERTIFICATE EXISTS for model; manuscript match PENDING |
| −6A | M14/M15: exact formula/label mapping **not yet verified** | Same PR #377 Arb job | `3d1ecb565fe71a81ddf715b101ae2ca0a98b63e8` | CERTIFICATE EXISTS for model; manuscript match PENDING |
| M14 Möbius determinant | M14 `subsec:det-mobius`, `eq:stirling-mobius-series`, `eq:mobius-dirichlet-exact` | PR #327 historic scope | not reconciled | NOT CERTIFIED under final-source scope |
| M14 dominant pole modulus | M14 `prop:dominant-pole-modulus`, `eq:dominant-pole-modulus` | Historic scope | not reconciled | NOT CERTIFIED under final-source scope |
| M15 cusp invariants | M15 `prop:cusp`, `eq:cusp-invariant`, `thm:cusp-all-orders` | Historic scope | not reconciled | NOT CERTIFIED under final-source scope |

The CI of #377 concerns the diagonal model, **not** a proof of the physical operator interpretation, infinite determinant, or all M14/M15 quantities. No precision may be inherited from a numerically similar expression without an exact symbolic identification.

## Mandatory acceptance test for each new nonzero numerical certificate

1. `ctx.prec = 3600000` and a per-value `assert x.rel_accuracy_bits() >= 3400000`.
2. Exact dyadic/rational endpoints enclose the Arb ball; verify both endpoints lie strictly within the same correctly scaled 1,000,001-significant-digit rounding cell, with ties excluded.
3. Persist digit string, exact endpoints, algorithm, proof of remainder bound, dependency versions, log, and SHA of the **exact HEAD** with successful CI.
4. For exact zero, integer, rational: provide exact proof or suitable absolute enclosure, never fictitious relative accuracy.
5. Do not classify documentation, conditional analytic bridges, finite test models or a successful CI on a different SHA as completed formalization.

## Next obligations

Extract and compare final-source defining formulas and their LaTeX labels before attaching any prior certificate; enumerate every applicable nonzero quantity; deduplicate shared constants; implement reproducible 3,600,000-bit Arb jobs and independent exact-endpoint rounding checks. The three open Draft heads #372, #373 and #376 had no pull-request workflow runs associated with their inspected commits before this documentation update. No manuscript edits or merge.
