# M16 §14.5 `cor:hol-eulerian`: evanescent moment series over the circle spectrum — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/HolonomyMomentSeries20261124.lean` (11 audited declarations).

## Starting point

`lean/Manuscript16/CERTIFICATION_SCOPE_20261117_V166_REACTIVE_HOLONOMY.md` lists for
`cor:hol-eulerian` as remaining: "connect spectral moments/product to closed forms, complex Eulerian
profile, limiting assertions"; for `eq:hol-integral`: "abstract spectral theorem, trace summability,
Tonelli and operator realisation". `ReactiveHolonomyV166` (merged) proves the single-value integral
`evanescent_scalar_moment` (`∫₀^∞ z e^{-2√b z} dz = 1/(4b)`, `b > 0`) and defines
`momentClosed a x c = (π/(4a)) sinh(2x)/(cosh(2x) − c)`, without connecting it to a sum over the
spectrum. The product side is done in `main` (#596, `HolonomyEulerProduct20261124`) and in the open
PR #597 (uniform convergence). No Lean statement in `lean/Manuscript16` sums over the circle
spectrum or uses the Mittag-Leffler expansion of the cotangent, and no open PR treats it (checked
24 Nov 2026, 23:08 UTC: the open PRs #597 (M16 `eq:hol-det` uniform convergence), #587, #584,
#582, #581, #565, #563, #394 (M11–M14) and #474 (shared Fredholm trace, M14; its `lean/Manuscript16`
files are byte-identical to `main`) do not touch this result). The obligation designated first in
the agent's brief, M16 `thm:dirac-maxwell-obstruction-164` (i)–(ii), is already closed in `main`
(#576, #585, #588) and was not re-proved.

## What is proved

Notation: `z = zeta a φ = φ + i a` (from #596), `circleEig a φ n = b_n = (n − φ)² + a²`, `n ∈ ℤ`;
`resolventClosed a φ = (π/a) sinh(2πa)/(cosh 2πa − cos 2πφ)`. Hypothesis `a > 0` throughout; `φ` real.

| Declaration | Statement |
|---|---|
| `circleEig_pos` | `b_n > 0` |
| `im_one_div_zeta_sub` | `Im 1/(z − m) = −a/((m − φ)² + a²)`, real `m` |
| `cotTerm_im` | `Im(1/(z − (n+1)) + 1/(z + (n+1))) = −a (1/b_{n+1} + 1/b_{−(n+1)})` |
| `im_cot_pi_zeta` | `Im cot(π(φ + i a)) = −sinh(2πa)/(cosh 2πa − cos 2πφ)` |
| `zeta_mem_integerComplement` | `z ∉ ℤ` |
| `circle_resolvent_hasSum` | **`∑_{n∈ℤ} 1/((n − φ)² + a²) = (π/a) sinh(2πa)/(cosh 2πa − cos 2πφ)`** (`HasSum` over `ℤ`) |
| `moment_series_hasSum` | **`∑_{n∈ℤ} 1/(4 b_n) = momentClosed a (πa) (cos 2πφ)`** |
| `evanescent_moment_hasSum` | **`∑_{n∈ℤ} ∫₀^∞ z e^{−2√b_n z} dz = momentClosed a (πa) (cos 2πφ)`** |
| `evanescent_trace_integral` | **`∫₀^∞ ∑_{n∈ℤ} z e^{−2√b_n z} dz = momentClosed a (πa) (cos 2πφ)`** (sum and integral interchanged; each term integrable on `(0, ∞)`, norms summable) |
| `half_phase_moment_ratio` | `(∑_n 1/(4 b_n(1/2))) / (∑_n 1/(4 b_n(0))) = tanh²(πa)` |
| `half_phase_moment_ratio_mul_det_limit` | the moment ratio times `((1/4 + a²)/a²) ∏_{n=1}^{N} pairRatio a (1/2) n` tends to `1` as `N → ∞` (with `holonomy_det_tendsto`, #596, and `half_product_reciprocal`) |

The sums are `HasSum` statements for the actual real series indexed by `ℤ` (unconditional
summation); the integrals are Lebesgue integrals on `Ioi 0`. No finite truncation, grid or
numerical surrogate is used.

Local check (pinned toolchain, 24 Nov 2026): `V166HolonomyPair`, `ReactiveHolonomyV166`,
`HolonomyEulerProduct20261124` and the new file compile with exit 0; the new file produces no
message (no warning, no error, no `Try this`); its 11 declarations depend only on `propext`,
`Classical.choice`, `Quot.sound`; the 29 axiom reports of the three imported modules contain only
these three. Local source SHA-256:
`f2ca8553225bcbaae89da81c3bb746b387047ec16e764b1a9943e7a8f57be94f`. The certifying run is
`.github/workflows/m16-hol-moment-series-20261124.yml` (exact-HEAD checkout, pinned toolchain,
compilation of the imported modules, `#print axioms` audit of 11/11 declarations and 29 imported
reports, failure on any warning or `Try this` message in the new file, artifacts).

## Published results cited, not re-proved

- Mittag-Leffler expansion of the cotangent, `π cot(πz) − 1/z = ∑_{n≥1} (1/(z − n) + 1/(z + n))`
  for `z ∉ ℤ`: classical; used through Mathlib `cot_series_rep'` and `summable_cotTerm`.
- Interchange of sum and integral under summable `L¹` norms: Mathlib
  `MeasureTheory.integral_tsum_of_summable_integral_norm`.
- Euler's sine product (only in the last corollary): through the merged
  `HolonomyEulerProduct20261124`.

## Not claimed

- That `b_n = (n − φ)² + a²` is the spectrum of a specific operator on the circle, that the series
  is an operator trace, or any spectral-theorem or trace-class statement: `b_n` is an explicit
  real sequence (the operator realisation of `eq:hol-integral` stays open).
- The complex Eulerian profile and the limiting assertions of `cor:hol-eulerian`: not treated here.
- Pointwise convergence of `∑_n z e^{−2√b_n z}` for each `z > 0` is not stated separately; the
  interchange theorem is used as stated.
- The correspondence of the symbols with the printed displays `cor:hol-eulerian` and
  `eq:hol-integral` of the 24 Nov 2026 `16.tex` (in particular `x = πa`, `c = cos 2πφ` in
  `momentClosed`) was not re-read in the source, which was not available to this run, and is to be
  confirmed.
