# M16 v16.5 §14.5, Theorem 14.5, equation (W1) — exact `W₁` and explicit optimal coupling (25 Nov 2026)

Source lock: `Manoscritto_16_5_Magnetic_Evanescent_Spectral_Transport_20261116(1).zip`, SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`. No manuscript source is modified; Manuscripts 11–15 are not touched.

## Obligation

`audits/manuscript16/v16_5_section14_5_finite_w1_bounds_20261117.md` (PR #342) lists Lean obligations (1)–(5) for the `W₁` statement of Theorem 14.5, none Lean-verified. `audits/M16_v165_Section14_GibbsScalarMean_20261117.md` (PR #343, file `Manuscript16/Section14GibbsScalarMean.lean`) certifies only the rational identity `2(E_r[n] − E_p[n]) = 4q/(1−q) − 2q/(3−q)` and leaves open: first moments, stochastic dominance, identification of the optimal `W₁` with the difference of the means. The `W∞` part of Theorem 14.5 is PR #600; it explicitly excludes `W₁`. No open PR treats `W₁` (checked 25 Nov 2026, 01:58 UTC).

## Lean module

`lean/Manuscript16/MaxwellGibbsW1OptimalCoupling20261125.lean`, 25 declarations, importing `Manuscript16.MaxwellGibbsTailObstruction20261125` (#600) for the laws `pₙ = (1−q)qⁿ`, `rₙ = 4(n+1)(n+3)qⁿ/C(q)`, `C(q) = 4(3−q)/(1−q)³`, the energy `Eₙ = 2n+1`, the coupling predicate `IsCoupling` and `W∞`. For `0 < q < 1`:

| Declaration | Statement |
|---|---|
| `hasSum_cube_mul_geometric` | `∑ n³qⁿ = q(1+4q+q²)/(1−q)⁴` (from Mathlib's Stirling-number formula) |
| `magnetic_energy_mean_hasSum` | `∑ Eₙ pₙ = 2q/(1−q) + 1` |
| `maxwell_energy_mean_hasSum` | `∑ Eₙ rₙ = 2q(3/(1−q) − 1/(3−q)) + 1` |
| `meanGap_pos`, `energy_mean_gap`, `two_meanGap_eq` | `Δ(q) = q(5−q)/((1−q)(3−q)) > 0`; difference of the energy means `= 2Δ(q) = 4q/(1−q) − 2q/(3−q)` |
| `lintegral_fst_of_coupling`, `lintegral_snd_of_coupling` | integral of a nonnegative marginal observable under any coupling, through the point masses of the marginal |
| `coupling_cost_ge` | every coupling `μ` of `p`, `r` on `ℕ × ℕ`: `∫⁻ |E_x − E_y| dμ ≥ 2Δ(q)` |
| `optMass`, `optMass_fst_hasSum`, `optMass_snd_hasSum` | `ν(m,n) = (1−q)³qⁿ(2(n−m)+3)/(3−q)` for `m ≤ n`, `0` otherwise; `∑ₙ ν(m,n) = pₘ`, `∑ₘ ν(m,n) = rₙ` (finite sum, `∑_{m≤n}(2(n−m)+3) = (n+1)(n+3)`) |
| `optCoupling_isCoupling`, `optCoupling_ae_le` | `ν` is a probability coupling of `p` and `r`, supported on `{m ≤ n}` |
| `optCoupling_cost` | `∫⁻ |E_x − E_y| dν = 2Δ(q)` |
| `wOneEnergy_eq`, `wOneEnergy_eq_closed` | **`W₁(p_E, r_E) = 2Δ(q) = 4q/(1−q) − 2q/(3−q)`**, infimum over all couplings attained by `ν` |
| `wOneEnergy_bounds` | the two-sided bounds of #342, `2q(5−q)/((1−q)(3−q)) ≤ W₁ ≤ 2q(4/(1−q) − 1/(3−q))`, as a consequence |
| `wOne_finite_wInf_infinite` | `W₁ < ∞` and `W∞ = +∞` (#600) |
| `tail_dominance` | `q^N ≤ ∑_{n≥N} rₙ` for every `N` (closed tail of #600) |

The coupling `ν` is the law of `(G₁, G₁ + G₂ + B·G₃)` with `G₁, G₂, G₃` independent with law `p` and `B` an independent Bernoulli variable with `P(B = 1) = 2/(3−q)` (the mixture of negative binomial laws of orders 2 and 3 that gives `r`); in Lean it is given directly by its masses, and only the masses are used.

`W₁` is defined as `⨅ μ, ⨅ (_ : IsCoupling μ p r), ∫⁻ x, ofReal |E x.1 − E x.2| ∂μ` (lower Lebesgue integral, no integrability premise).

## Not claimed

Electromagnetic energy flux or physical spatial transport; couplings on `ℝ × ℝ` of the push-forward laws (the energy axis enters through the cost `|E_x − E_y|` on `ℕ × ℕ`); the index-axis value `W₁ = Δ(q)` (same argument, not stated). The correspondence with the printed display (W1) of Theorem 14.5 in the current `16.tex` must still be checked against the source, which was not available to this run; the printed form used here, `4q/(1−q) − 2q/(3−q)`, is the one recorded by #343.

## Verification

- Local, pinned toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`: the three imported modules and the new file compile with exit 0; no message from the new file; 25/25 declarations and 30 imported reports depend only on `propext`, `Classical.choice`, `Quot.sound`. Source SHA-256 `a591280b6bbd2c51470bacc34180dbbcf4d2d746b627d11226453634b6d54d90`.
- Exact symbolic cross-check (SymPy) of `∑ n³qⁿ`, of both means, of `Δ(q)` and of the upper bound.
- Certifying run: `.github/workflows/m16-gibbs-w1-optimal-coupling-20261125.yml` (exact-HEAD checkout, pinned toolchain and Mathlib, `#print axioms` audit of 25 declarations and 30 imported reports, failure on any warning or `Try this` in the new file, artifacts).

No numerical certificate is needed: every constant is an exact rational function of `q`.
