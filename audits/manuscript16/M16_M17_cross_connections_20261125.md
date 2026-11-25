# M16 Proposition 15.1 and M17 Proposition 10.1 / Corollary 10.2 — Lean 4 record (25 Nov 2026)

## Reference packages

| Package | SHA-256 |
|---|---|
| `Manuscript_16_20261125_CROSS_CONNECTIONS.zip` | `a8a7264928c4c3bb8c46a27b7891c27585aa93a7aefdf10819b44c9e5474868c` |
| `16.tex` | `66d70c995642b704b4a7a3e4cf3cba95a5a94dd93ae76807a49dc65f89fc9f87` |
| `Manuscript_17_20261125_CROSS_CONNECTIONS.zip` | `d77e9116eaa0e329c296b75ffc87dce4dadde3ae349a7d2ed7e46908a7aebfc2` |
| `Cyclohedral.tex` | `338061e9b2c8581ec982fecc38935a6dc048af1dc6ac635f9ed263bc0628cf86` |
| `12.tex` (definition of `F_crit`, line 2637; `eq:cross-vaczero`, `eq:cross-Qzero`) | `67077497bc9095fade4574720628b42ea22fe49f2027d5b075ee9baa45b114d9` |

Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`. Modules: `lean/Manuscript16/QuarticPartitionSusceptibility20261125.lean`, `lean/Manuscript17/CrossConnections20261125.lean`; workflow `m16-m17-cross-connections-20261125.yml`.

`F_crit(λ) = (1/(2√π)) ∫_ℝ du / exp(u⁴/40 + 6λu²)` is taken verbatim from Manuscript 12 (`12.tex`, line 2637, `eq:cross-Fcrit`).

## M16, Section 15, `prop:cross-suscept16`

| Label | Statement | Lean declaration | Status |
|---|---|---|---|
| `eq:cross-law16` | `dη_λ = du / (2√π F_crit(λ) exp(u⁴/40 + 6λu²))`, a probability measure | `eta`, `density`, `isProbabilityMeasure_eta`, `integral_eta` | proved |
| `eq:cross-logder16` | `(log F_crit)' = -6 ∫ u² dη_λ` | `hasDerivAt_log_Fcrit` | proved (differentiation under the integral sign with an explicit quartic–Gaussian dominating function) |
| `eq:cross-loghess16` | `(log F_crit)'' = 36 Var_{η_λ}(u²) > 0` | `hasDerivAt_deriv_log_Fcrit`, `varEta_eq`, `varEta_pos`, `cross_loghess16` | proved |
| `eq:cross-ode16` | `F_crit'' - 720 λ F_crit' - 360 F_crit = 0` | `mom_ibp` (integration by parts of `d/du[u e^{-V}]` on ℝ), `Fcrit_ode` | proved |

All four equations are proved for every real `λ`, with no premise.

## M17, Section 10, `prop:cross-lem17` and `cor:cross-lem17`

| Label | Content | Lean declaration | Status |
|---|---|---|---|
| `eq:cross-lemLength` | lobe arclength `= 2 ∫₀¹ dt/√(1−t⁴)` | `ellPlus` (definition of the integral) | classical polar arclength of the lemniscate; published result cited, not formalized |
| `eq:cross-lemAmp` | `ℓ₊ = √2 K(1/√2) = 2𝒜_E` | — | classical (`√2 K(1/√2)`); `𝒜_E` belongs to Manuscript 15; not formalized |
| `eq:cross-lemF` | `ℓ₊ = 2√(π/5) F_crit(0)²` | `Fcrit_zero`, `lemF_gamma` (no premise); `cross_lemF` (premise `GaussLemniscate`) | the new content `2√(π/5) F_crit(0)² = Γ(1/4)²/(2√(2π))` is proved; Gauss's evaluation `2 ∫₀¹ dt/√(1−t⁴) = Γ(1/4)²/(2√(2π))` enters as a published result cited |
| `eq:cross-lemVac` | `√M p_{E,M}(M/12)² → (2/ℓ₊)√(π/5)` | `cross_lemVac` | conditional on `eq:cross-vaczero` of Manuscript 12 (not certified here) and `GaussLemniscate` |
| `eq:cross-area17` | `Area_{g_Φ} = π(1 − arctan z₀/(2z₀))`, `z₀ = i/√2` | `arctan_z0` (`arctan(i/√2) = i log(1+√2)`, principal branch of Mathlib's `Complex.arctan`), `arctan_z0_div`, `cross_area17` | proved; the right-hand side `π(1 − log(1+√2)/√2)` is the area of `eq:m17-area`, proved in Lean in #593 |
| `eq:cross-Q17` | `√M (𝒬_M(1/12) − 1)² → √(π/5) / (2(π²+1)² ℓ₊)` | `cross_Q17` | conditional on `eq:cross-Qzero` of Manuscript 12 (not certified here) and `GaussLemniscate` |

`Fcrit_zero` also proves Manuscript 12's `eq:cross-Fzero`, `F_crit(0) = 40^{1/4} Γ(1/4)/(4√π)`, which Manuscript 17 uses.

## Axiom audit

Local compilation on the pinned toolchain: both modules exit 0 with no warning; all 20 audited declarations (12 in M16, 8 in M17) depend only on `propext`, `Classical.choice`, `Quot.sound`. The certifying run is the GitHub workflow on the exact PR head.
