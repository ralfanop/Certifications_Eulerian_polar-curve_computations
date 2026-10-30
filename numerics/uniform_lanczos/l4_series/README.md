# Task L4 — generation of `lean/UniformLanczos/HigherProfileCoefficients.lean`

Exact rational series arithmetic (Python `fractions`, no floating point):

* `l4_series.py` — Bernoulli numbers, the series of Λ′(s) = Σ B₂ₖ s^{2k−1}/(2k)!, its reversion I′,
  the Wallis moments and Φ(a) = Σ cₖ W_{k+1} a^{k+1}, and the reversion F(α) = a²/4 as a series in α.
  Run it to print Lp, Ip, Φ (in A = a²) and F.
* `l4_gen.py` — the exact quotient polynomials `Rcomp = (LpPoly∘IpPoly − id)/x¹⁵` (78 terms) and
  `R2 = (GPoly∘PhiPoly − id)/A⁸` (42 terms), and the coefficient-sum bounds used in Lean.
* `l4_template.lean` + `l4_module.py` — the Lean module is the template with the polynomials inserted
  (`python3 l4_module.py OUT.lean` reproduces `HigherProfileCoefficients.lean` byte for byte).

Every polynomial identity is re-verified inside Lean by `ring`; every bound by `linarith` from explicit
monomial bounds. The Lean certificate (39 declarations, only `propext`, `Classical.choice`, `Quot.sound`)
is recorded in `lean/logs/uniform_lanczos_axioms.log` (100 declarations, with the 61 earlier ones) and
`lean/logs/uniform_lanczos_l4_certification.json` (SHA-256 of source and compiled object).
