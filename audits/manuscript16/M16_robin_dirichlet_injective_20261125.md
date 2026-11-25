# M16 v16.5 §14.2, Proposition 14.2: Dirichlet and Robin Green operators injective, strictly positive, with dense range — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletInjective20261125.lean` (17 audited declarations), SHA-256
`e2ac547e5743055dede0269dce067e1efca99d7d75a811c77dbdb5535e04e7bb`. It imports `Mathlib` and
`Manuscript16.RobinDirichletPositive20261125` (PR #606, head `bfbce14106db70d48952e00544ac1ab01dadbe65`,
source SHA-256 `bdfd818ada54b17c72df2a031a06fde742f6c5f8db029cc61a3228924b3e681c`), which imports
`Manuscript16.RobinDirichletL2Bounded20261125` (PR #605, `303e9028…`) and, through it,
`Manuscript16.RobinDirichletRankOne20261125` (PR #603, `78663893…`). This branch is stacked on #606
(and therefore on #605 and #603). Nothing of #603, #605 or #606 is re-proved.

## Starting point

#606 factors the Dirichlet Green operator as `K_D = W† W` on `L² = L²((0,∞); ℂ)`, with
`(W f)(s) = ∫₀^∞ ψ(w,s) f(w) dw`, `ψ(w,s) = 1_{s ≤ w} e^{−a(w−s)}`, proves that `K_D` and
`K_R = K_D + P_a` are positive and self-adjoint, and lists **strict positivity and injectivity** as not
claimed. Proposition 14.2 presents `K_D`, `K_R` as the resolvents `(H_D − t)⁻¹`, `(H_R − t)⁻¹` of
self-adjoint operators; a resolvent is injective with dense range, so these are necessary properties of
the printed Green operators. No open PR treats them (checked 25 Nov 2026, 08:04 UTC: #597–#602 concern
§14.1 and §14.5, #603–#606 list injectivity as not claimed or do not mention it, #474 concerns
`SpecialImaginaryPoint`, the others M11–M14).

The first obligation of the run brief, `thm:dirac-maxwell-obstruction-164` (i)–(ii), is closed in `main`
by #576, #585 and #588 (see the register) and was not re-proved.

## Method

Let `g_f(w) = e^{−aw} f(w)`, integrable on `(0,∞)` by Cauchy–Schwarz (`L2.integrable_inner`), and
`G_f(s) = ∫_{(s,∞)} g_f`. Then for every real `s`

`(W f)(s) = e^{as} G_f(s)`  (`Wfun_eq_tail`),

and `G_f` is continuous (dominated convergence with bound `|g_f|`; Lebesgue measure has no atoms).
If `W f = 0` in `L²`, then `G_f = 0` almost everywhere on `(0,∞)`, hence on `(0,∞)` by continuity
(`Measure.eqOn_open_of_ae_eq`), hence on `[0,∞)`; for `s ≤ 0`, `G_f(s) = G_f(0)`. So `∫_S g_f = 0` for
every `S` in the π-system `{(s,∞) : s ∈ ℝ}`, which generates the Borel σ-algebra; the sets with
`∫_S g_f = 0` are closed under complements and countable disjoint unions, so `∫_S g_f = 0` for every Borel
`S` (`MeasurableSpace.induction_on_inter`), and `g_f = 0`, hence `f = 0`, almost everywhere. No
differentiation theorem, Fourier transform or spectral theorem is used.

Consequences: `⟪f, K_D f⟫ = ‖W f‖²` (#606) gives `Re ⟪f, K_D f⟫ > 0` for `f ≠ 0`; adding
`Re ⟪f, P_a f⟫ ≥ 0` (#603) gives the same for `K_R` when `β < a`; strict positivity implies injectivity;
for a self-adjoint injective bounded operator, `(range T)ᗮ = ker T† = ker T = 0`, so the range is dense.

## Lean statements (17 audited declarations)

| Declaration | Statement |
|---|---|
| `integrable_weighted` | `g_f` integrable on `(0,∞)` |
| `Wfun_eq_tail` | `(W f)(s) = e^{as} G_f(s)` for every `s` |
| `continuous_tail` | `G_f` continuous |
| `tail_of_nonpos` | `G_f(s) = ∫₀^∞ g_f` for `s ≤ 0` |
| `tail_eq_zero_of_Wop` | `W f = 0 ⇒ G_f ≡ 0` |
| `setIntegral_weighted_eq_zero` | `W f = 0 ⇒ ∫_S g_f = 0` for every Borel `S` |
| `eq_zero_of_Wop`, `Wop_injective` | `W f = 0 ⇒ f = 0`; `W` injective |
| `re_inner_KDop_pos` | `f ≠ 0 ⇒ Re ⟪f, K_D f⟫ > 0` |
| `re_inner_KRop_pos` | `β < a`, `f ≠ 0 ⇒ Re ⟪f, K_R f⟫ > 0` |
| `injective_of_re_inner_pos` | strict positivity ⇒ injectivity |
| `KDop_injective`, `KRop_injective` | `K_D`, `K_R` (`β < a`) injective |
| `denseRange_of_isSelfAdjoint` | self-adjoint and injective ⇒ dense range |
| `denseRange_KDop`, `denseRange_KRop` | `K_D`, `K_R` (`β < a`) have dense range |
| `prop14_2_injective` | manuscript form: `c = ‖κ‖²`, `β > 0`, `t < c − β²`, `a = √(c − t)`; `W`, `K_D`, `K_R` injective, `K_D`, `K_R` strictly positive with dense range |

## Not claimed

The self-adjoint realisations `H_D`, `H_R` on `H²(0,∞)` and the identification `KDop = (H_D − t)⁻¹`,
`KRop = (H_R − t)⁻¹`; any coercivity bound `Re ⟪f, K f⟫ ≥ c ‖f‖²`; surjectivity or non-surjectivity;
Schatten-ideal membership; the essential spectrum; any Maxwell or geometric identification. The match
with the printed Proposition 14.2 of the current `16.tex` still has to be checked against the source,
which was not available to this run.

## Verification

- Local, pinned toolchain (Mathlib checked out at `0272bbe1` in `.lake/packages/mathlib`, cache from
  `lake exe cache get`): the three imported modules and the new module compile with exit 0; the new module
  produces no error, warning or `Try this`; 17/17 declarations depend only on `propext`,
  `Classical.choice`, `Quot.sound`. The compile-and-audit step of the new workflow was run locally with
  success (`SUCCESS: 17 theorems and 143 imported declarations; standard axioms only`).
- Certifying run: `.github/workflows/m16-robin-dirichlet-injective-20261125.yml` (exact-HEAD checkout and
  SHA assertion, pinned toolchain and Mathlib pin asserted, compilation of the three imported modules and
  of the new module, failure on any error, warning, `Try this`, `sorryAx`, `Lean.ofReduceBool` or
  non-standard axiom, artifact with per-declaration axiom lists).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
