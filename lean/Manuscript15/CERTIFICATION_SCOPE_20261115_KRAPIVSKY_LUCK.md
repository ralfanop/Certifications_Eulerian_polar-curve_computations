# M14 and M15 — Krapivsky–Luck revision certification scope (2026-11-15)

Author-supplied authoritative archives:
- Manuscript_14_Krapivsky_Luck_20261115(1).zip, SHA-256 `7b784e61c36e125ea8015ade2993ca0b1f344027da5eedba43879e141680b62e`.
- Manuscript_15_Krapivsky_Luck_20261115(1).zip, SHA-256 `d44a7ac1d0d9501bc7d9aed5d345afb1dcd11a18c0d4ec540806e9c16bc1980c`.

M14 subsection det-mobius, equations (97a–d), and M15 §6.6 introduce the common Stirling-remainder Möbius identity. Historical ledgers, including M15 PR #325 and its unresolved obligations, remain applicable to unchanged statements.

| Obligation | Candidate coverage in this branch | Still open |
|---|---|---|
| Möbius divisor cancellation | actual arithmetic function, weighted finite fibres, infinite regrouping assuming summability of the double family | prove summability for the actual analytic kernel, including the inverse-square bound and product-series argument |
| Binet and Laplace–resolvent identity | none | identify actual Stirling remainder, change variables, justify exchanges of integral and series |
| Sine-integral evaluation of surviving kernel | none | prove Laplace integral evaluation and specialization at 2π |
| M15 linear/quadratic profile moments | pointwise squared-sinc trigonometric identity | actual sine integral definition, improper/finite integrals, energy and tail |
| M15 prime-sum regularization | not certified | distinguish rigorous convergent coefficient/log-zeta series from heuristic prime-zeta regularization; do not assert analytic continuation |
| New explicit numerical constants | not certified on this branch | fixed 3,600,000 working bits, ≥3,400,000 relative accuracy individually, strict exact endpoints in the 1,000,001-significant-digit decimal rounding cell; store exact endpoints and digits with exact-HEAD artifacts |

All Lean results are candidates until compilation and axiom audit succeed on this exact HEAD. No numerical certificate is claimed. No figures or manuscript files modified; no merge authorized.
