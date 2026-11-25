# M16 v16.5 §14.5, Theorem 14.5: exact Maxwell–Gibbs upper tail and `W∞` obstruction — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/MaxwellGibbsTailObstruction20261125.lean` (22 audited declarations).

## Starting point

`lean/Manuscript16/CERTIFICATION_SCOPE_20261117_V166_REACTIVE_HOLONOMY.md` states that the 16.5
obligations remain open. For Theorem 14.5 of the author-approved 16.5 archive
(`Manoscritto_16_5_Magnetic_Evanescent_Spectral_Transport_20261116(1).zip`, SHA-256
`4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`), the analytic audit
`audits/manuscript16/v16_5_section14_5_exact_tail_audit_20261117.md` lists six Lean obligations, all
unproved: (i) geometric sums for `q^k`, `k q^k`, `k² q^k`; (ii) termwise rearrangement and tail formula;
(iii) probability normalisation; (iv) coupling marginal event inequality; (v) polynomial divergence;
(vi) energy-axis scaling. In `main` only the generating function `∑ wₙ qⁿ = 4(3−q)/(1−q)³`
(`V165ResonanceInfinite.resonance_hasSum`) and the finite identity with tail polynomial
(`V165ResonanceGenerating`) existed. No open PR treats these laws, their tails or couplings (checked
25 Nov 2026, 01:00 UTC: open PRs #599, #598, #597 (M16 §14.5 v16.6 holonomy), #587, #584, #582, #581,
#565, #563, #474, #394 (M11–M14)).

The obligation designated first in the agent's brief, M16 `thm:dirac-maxwell-obstruction-164` (i)–(ii),
is already closed in `main` (#576, #585, #588) and was not re-proved.

## Notation

`0 < q < 1`; `wₙ = 4(n+1)(n+3)` (`Manuscript16.V165.resonanceWeight`); `C(q) = 4(3−q)/(1−q)³`
(`maxwellNorm`); magnetic index law `pₙ = (1−q) qⁿ` (`magneticLaw`); Maxwell index law
`rₙ = wₙ qⁿ / C(q)` (`maxwellLaw`); energy axis `Eₙ = 2n + 1` (`energy`).

## What is proved

| Declaration | Statement | Obligation |
|---|---|---|
| `maxwellNorm_pos`, `resonanceWeight_pos`, `magneticLaw_nonneg`, `maxwellLaw_nonneg` | positivity | — |
| `magneticLaw_hasSum`, `maxwellLaw_hasSum` | `∑ pₙ = 1`, `∑ rₙ = 1` | (iii) |
| `magnetic_tail_hasSum` | `∑ₖ p_{k+N} = q^N` | (i), (ii) |
| `maxwell_tail_hasSum` | **`∑ₖ r_{k+N} = 4q^N/C(q) · ((N+1)(N+3)/(1−q) + (2N+4)q/(1−q)² + q(1+q)/(1−q)³)`** (`maxwellTailClosed`), from Mathlib `hasSum_geometric_of_norm_lt_one`, `hasSum_coe_mul_geometric_of_norm_lt_one`, `hasSum_sq_mul_geometric_of_norm_lt_one` | (i), (ii) |
| `upper_tail_hasSum_iff` | `∑ₙ 1_{n ≥ K} fₙ = a ⇔ ∑ₖ f_{k+K} = a` | (ii) |
| `measure_preimage_eq_ofReal` | for a measurable `X : Ω → ℕ` with point masses `P(X = n) = pₙ`, `P(X ∈ s) = ∑_{n∈s} pₙ` (countable additivity) | (iv) |
| `magnetic_tail_prob`, `maxwell_tail_prob` | `P(X ≥ N) = q^N`, `P(Y ≥ N) = maxwellTailClosed q N` as events | (ii), (iv) |
| `tail_ratio_lower`, `tail_ratio_tendsto` | `4(N+1)(N+3)/(C(q)(1−q)) ≤ P(Y ≥ N)/P(X ≥ N)`, and the ratio tends to `+∞` | (v) |
| `no_bounded_displacement` | **on any measure space, if `P(X = n) = pₙ` and `P(Y = n) = rₙ` for all `n` (`X` measurable), then for every real `D` it is false that `|X − Y| ≤ D` almost everywhere** | (iv), (v) |
| `no_bounded_energy_displacement` | the same for `|E_X − E_Y|` | (vi) |
| `essSup_displacement_eq_top`, `essSup_energy_displacement_eq_top` | `ess sup |X − Y| = +∞`, `ess sup |E_X − E_Y| = +∞` | (iv)–(vi) |
| `IsCoupling`, `wInfIndex`, `wInfEnergy` | couplings: probability measures on `ℕ × ℕ` with marginals `p`, `r`; `W∞` = infimum over couplings of the essential supremum of the displacement | — |
| `wInfIndex_eq_top`, `wInfEnergy_eq_top` | **`W∞(p, r) = +∞` on the index axis and on the energy axis** | Theorem 14.5 |
| `pmfOfReal`, `pmfOfReal_toMeasure_singleton`, `exists_coupling` | the independent coupling (product of the two laws) is a coupling: the infimum is not over an empty set | — |

The obstruction is proved as in the audit note, without assuming that a bounded coupling exists: if
`|X − Y| ≤ D` a.e., with `M = ⌈D⌉` and `N = M + T`, the event `{Y = N}` is a.e. contained in
`{X ≥ T}`, hence `r_N ≤ q^T`, i.e. `w_N q^M ≤ C(q)`; the choice `T = ⌈C(q)/(4q^M)⌉` contradicts
`w_N ≥ 4(T+1)`. No statement on pointwise masses replaces the marginal event inequality.

Local check (pinned toolchain, 25 Nov 2026): the two imported repository modules
(`Manuscript16/V165ResonanceGenerating`, `Manuscript16/V165ResonanceInfinite`) and the new file compile
with exit 0; the new file produces no message (no warning, no error, no `Try this`); its 22 declarations
depend only on `propext`, `Classical.choice`, `Quot.sound`; the 8 axiom reports of the imported modules
contain only these three. Local source SHA-256:
`b3feb0ed0b3362a232c01d97f2459c9471a2748d2d2b3fc337d3bdcb4152e3a0`. The certifying run is
`.github/workflows/m16-gibbs-tail-winf-obstruction-20261125.yml` (exact-HEAD checkout, pinned toolchain
and Mathlib, compilation of the 2 imported modules, `#print axioms` audit of 22/22 declarations and 8
imported reports, failure on any warning or `Try this` message in the new file, artifacts).

## Published results cited, not re-proved

Geometric series and their first two differentiated forms (Mathlib); countable additivity of measures
and the product of probability measures (Mathlib).

## Not claimed

- Any identification of the Wasserstein distance between these index laws with electromagnetic energy
  flux or physical spatial transport (as in the audit note).
- `W∞` for the push-forward laws regarded as measures on `ℝ` with couplings on `ℝ × ℝ`: the energy-axis
  statements are proved for couplings of the index laws (and for arbitrary random variables with these
  index laws), measuring the displacement `|E_X − E_Y| = 2|X − Y|`.
- The finite `W₁` bounds of `audits/manuscript16/v16_5_section14_5_finite_w1_bounds_20261117.md` (separate
  obligation, not treated here).
- The correspondence with the printed statement of Theorem 14.5 in the current `16.tex` (labels and
  numbering of the 24 Nov 2026 package) was not re-read in the source, which was not available to this
  run; the statement used is the one recorded in the 17 Nov 2026 audit note, and is to be confirmed.
