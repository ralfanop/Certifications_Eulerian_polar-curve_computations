# M16 §13 `eq:mixed-lower-series-164`, `eq:mixed-upper-series-164`: Maxwell series for every real `p` — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/MaxwellLowerUpperSeries20261124.lean` (12 audited declarations).
Stacked on #589 (`DiracMaxwellSchattenThreshold20261124`), itself stacked on #588: the parent of this
branch is the #589 head `3bcc3980d43af708958559c459e0781c5aef0271`.

## Starting point

`docs/manuscript16/V166_FROZEN_SECTION13_IDENTITY_RECONCILIATION_20261118.md`, table C, records as open:

- `mixed-lower-series-164` (`∑ 2(ℓ²−1)/(4(ℓ+1))^p`): "General p≤3 and spectral-operator transfer open";
  `main` has only the `p = 3` nearest-mode series (`V165SchattenThirdNonsummable.third_shell_nonsummable`);
- `mixed-upper-series-164` (`≤ 4/(2ℓ)^p × ∑ j^{−p}`, `p > 1`): "full infinite upper estimate for actual
  integer-index series remains open".

#589 proves `∑ᵢ |wᵢ|ᵖ < ∞ ⇔ p > 3` for the whole spectral list of the coefficient-space
`L₀ = W_R ⊕ D₃` (#588), but its divergence half uses only the Dirac shells: on the Maxwell modes it
proves convergence for `p > 3` (`maxwell_summable`) and nothing for `p ≤ 3`. No open PR treats the
Maxwell lower series or the infinite upper series (checked 24 Nov 2026, 19:55 UTC: open PRs #588, #589,
#592, #593 and the M11–M15 PRs).

## What is proved

All statements are on the actual index type `MaxwellIndex` of #422/#588 (`ℓ = l + 2`, `k ∈ ℤ \ {0, −ℓ}`,
multiplicity `2(ℓ² − 1)`, `|wᵢ| = 1/(4|k||ℓ+k|)`), for every real `p` unless stated.

| Declaration | Statement |
|---|---|
| `kOne`, `abs_maxwellWeight_nearest` | nearest mode `k = 1`: `|w| = 1/(4(ℓ+1))` |
| `lowerShell`, `lowerShell_nonneg`, `mult_cast` | `lowerShell p l = 2(ℓ²−1)·(4(ℓ+1))^{−p}`, `2(ℓ²−1) = 2(ℓ−1)(ℓ+1)` |
| `lowerShell_le_fiber_tsum` | if the `ℓ`-fiber sum converges, it is `≥ 2(ℓ²−1)(4(ℓ+1))^{−p}` |
| `lowerSeries_summable_iff` | **`∑_{ℓ≥2} 2(ℓ²−1)/(4(ℓ+1))^p < ∞ ⇔ p > 3`** (for `p ≤ 3` the terms dominate `1/(96(ℓ+1))`) |
| `lowerSeries_summable_of_maxwell` | Maxwell `p`-summability implies summability of the lower series |
| `maxwell_summable_iff` | **`∑_{Maxwell} |wᵢ|ᵖ < ∞ ⇔ p > 3`** (with #589 `maxwell_summable`) |
| `maxwellWeight_memℓp_iff` | the Maxwell part of the diagonal of `L₀⁻¹` is in `ℓᵖ` exactly for `p > 3` (`p > 0`, Mathlib `Memℓp`) |
| `lowerSeries_le_maxwell_tsum` | `p > 3`: `∑_ℓ 2(ℓ²−1)/(4(ℓ+1))^p ≤ ∑_{Maxwell} |wᵢ|ᵖ` |
| `zetaZ_eq_two_mul` | `p > 1`: `∑_{n∈ℤ} |n|^{−p} = 2 ∑_{j≥1} j^{−p}` |
| `upperSeries_le` | **`p > 1`, every `ℓ` and every multiplicity label: the actual series over `k ∈ ℤ \ {0, −ℓ}` converges and `∑_k |w_{ℓ,k}|ᵖ ≤ 4(2ℓ)^{−p} ∑_{j≥1} j^{−p}`** |

Local check (pinned toolchain, 24 Nov 2026): the eleven imported project modules and the new file
compile with exit 0, no warning and no error in the new file; all 12 declarations depend only on
`propext`, `Classical.choice`, `Quot.sound` (`kOne` on `propext`, `Quot.sound`); the 126 axiom reports
printed by the imported modules contain only these three. Source SHA-256:
`ac9cd6600cb801258502ce06d8f804bb42cdc38bce690c3db6f556078e93d6b8`. Certifying run:
`.github/workflows/m16-maxwell-lower-upper-series-20261124.yml` (exact-HEAD checkout, pinned toolchain,
rebuild of the imported modules, `#print axioms` audit of 12/12 declarations, failure on any warning,
artifacts).

## Not claimed

- The forms above are those recorded in the reconciliation ledger; the source `16.tex` was not
  available to this run, so the correspondence with the printed displays is to be confirmed against the
  manuscript.
- Operator statements: `diag(w) ∈ S_p ⇔ w ∈ ℓᵖ` and the ideal property of `S_p` are published results
  cited (Simon 2005, Ch. 2), not formalized (Mathlib has no Schatten classes at the pinned commit).
- As in #588, #589, the unitary identification of `ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)` is a published
  input; no geometric statement on `S³` is derived.

## Residual obligations

Every `det₄` statement (`eq:mixed-det4-164`, `eq:mixed-det4-criterion-164`): classification pending a
decision of the scientific lead (see #592).
