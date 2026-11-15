# Manuscripts 11 and 12 — revision 2026-11-15: Krapivsky–Luck

Author-supplied ZIPs, not external manuscript versions:
- Manuscript_11_Krapivsky_Luck_20261115(1).zip, SHA-256 `4e1a28492c9e58bca106bdc97f82ba1d30f48a15b4f3c5175e5ea02e34fed1a3`.
- Manuscript_12_Krapivsky_Luck_20261115(1).zip, SHA-256 `671ebf26fecbfcbb77e3ce705d84b4af2a61ed73afb24a2c3aeb21ec62341c6b`.

Source: P. L. Krapivsky and J. M. Luck, *Zeta-regularization and natural boundaries: Sums and products of integers and primes*, J. Phys. A (2026), DOI 10.1088/1751-8121/aebe85; arXiv:2606.24536, Eq. (1.6) and Appendix A. The classical analytic identities are separated from the authors' proposed regularization; no value for a divergent prime sum is asserted.

| Statement | Candidate Lean scope |
|---|---|
| M11 (48a), M12 (56b) | Arbitrary positive interval via the existing proved primitive EulerianCert.Energy.G, avoiding a singularity at zero. |
| M11 (48b) | Both actual linear and squared-sinc integral representations of C. |
| M11 (48c), M12 (56c) | Tail integral with explicit real-line total energy hypothesis; derives integrability from nonzero total, not a fictitious integral convention. |
| M12 (56a) | Actual real representative of the normalized kernel, central window energy. |
| M12 Rayleigh quotient | Open: construct/identify the L² indicator multiplication and compressed projection, show positive contraction and evaluate its quadratic form. |
| Real-line total energy | Open in this module: discharge the classical Plancherel input; existing Bridge.PaleyWiener proof takes a stated Plancherel hypothesis in a separate pinned Lake project. |
| C and S numerical certification | Open; no new numerical output at lower precision. Required working bits 3,600,000, individual relative accuracy ≥3,400,000, exact strict decimal rounding-cell containment at 1,000,001 significant digits, exact head artifacts. |

The separate open M14/M15 Möbius regrouping PR #327 is not duplicated. No manuscript or figure modification. All new theorem declarations remain candidates pending exact-head CI and standard axiom audit. No merge.

