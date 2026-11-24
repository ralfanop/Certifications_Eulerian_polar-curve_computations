# M16 §14.5 `eq:hol-det`: Euler evaluation of the paired holonomy product — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/HolonomyEulerProduct20261124.lean` (12 audited declarations).

## Starting point

`lean/Manuscript16/CERTIFICATION_SCOPE_20261117_V166_REACTIVE_HOLONOMY.md` lists for `eq:hol-det`
(v16.6, §14.5): done, "exact paired numerator cancellation"; remaining, "uniform convergence and Euler
sine product applied to the circle spectrum". `docs/manuscript16/V166_HOLONOMY_PAIRED_CONVERGENCE_20261119.md`
records that the absolute summability of the paired deviations is in Lean
(`V166HolonomyPair.paired_deviation_summable`, merged) and that "the logarithmic/product argument and
Euler closed evaluation remain separate Lean obligations". `ReactiveHolonomyV166` (merged) defines the
closed form `productClosed x c = (cosh 2x − c)/(cosh 2x − 1)` and proves scalar identities for it, without
connecting it to the product. No Lean statement using Euler's sine product exists in `lean/Manuscript16`,
and no open PR treats `eq:hol-det` (checked 24 Nov 2026, 21:00 UTC: the eight open PRs concern M11–M14, `formalizations/peters2024` and
shared Fredholm-trace files (#474); none touches `lean/Manuscript16`).

## What is proved

Notation of the merged files: `pairRatio a φ n = ((n−φ)²+a²)((−n−φ)²+a²)/(n²+a²)²`, `z = φ + i a`.

| Declaration | Statement |
|---|---|
| `zeta`, `normSq_zeta`, `zeta_ne_zero` | `z = φ + i a`, `|z|² = φ² + a²`, `z ≠ 0` for `a ≠ 0` |
| `normSq_factor` | `|1 − z²/m²|² = ((m−φ)²+a²)((m+φ)²+a²)/m⁴`, real `m ≠ 0` |
| `pairRatio_eq_normSq` | `pairRatio a φ m = |1 − z²/m²|² / (1 + a²/m²)²` |
| `pairProduct_eq` | `∏_{n=1}^{N} pairRatio a φ n = |∏_{n=1}^{N}(1 − z²/n²)|² / (∏_{n=1}^{N}(1 + a²/n²))²` |
| `sine_factor_tendsto` | `∏_{n=1}^{N}(1 − z²/n²) → sin(πz)/(πz)`, `z ≠ 0` (from Mathlib `Complex.tendsto_euler_sin_prod`) |
| `sinh_factor_tendsto` | `∏_{n=1}^{N}(1 + a²/n²) → sinh(πa)/(πa)`, `a ≠ 0` |
| `normSq_sin_pi_zeta` | `|sin(π(φ + i a))|² = sin²(πφ) + sinh²(πa)` |
| `paired_product_tendsto` | **`a > 0`, every real `φ`: `∏_{n=1}^{N} pairRatio a φ n → a²(sin²(πφ) + sinh²(πa)) / ((φ²+a²) sinh²(πa))`** |
| `productClosed_eq` | `productClosed (πa) (cos 2πφ) = (sin²(πφ) + sinh²(πa)) / sinh²(πa)` |
| `holonomy_det_tendsto` | **`a > 0`, every real `φ`: `((φ²+a²)/a²) · ∏_{n=1}^{N} pairRatio a φ n → (cosh 2πa − cos 2πφ)/(cosh 2πa − 1)`** (unpaired `n = 0` factor included) |
| `holonomy_det_limit_ge_one` | the limit is `≥ 1`, with equality iff `sin(πφ) = 0` |

The limits are `Filter.Tendsto … atTop` statements for the actual real sequences of partial products; no
finite-dimensional or numerical surrogate is used.

Local check (pinned toolchain, 24 Nov 2026): `V166HolonomyPair`, `ReactiveHolonomyV166` and the new file
compile with exit 0; the new file has no warning and no error; its 12 declarations depend only on
`propext`, `Classical.choice`, `Quot.sound`; the 17 axiom reports of the two imported modules contain only
these three. Source SHA-256 is recorded by the certifying run:
`.github/workflows/m16-hol-det-euler-product-20261124.yml` (exact-HEAD checkout, pinned toolchain,
compilation of the imported modules, `#print axioms` audit of 12/12 declarations, failure on any warning
in the new file, artifacts).

## Published results cited, not re-proved

- Euler's product `sin(πz) = πz ∏_{n≥1}(1 − z²/n²)`: classical; used through Mathlib
  `Complex.tendsto_euler_sin_prod`.

## Not claimed

- That `∏ pairRatio` is the determinant of the holonomy operator on the circle spectrum (operator
  determinant, spectral theorem, trace-class membership): not formalized.
- Uniform convergence in `(a, φ)` on compact sets (written argument in
  `V166_HOLONOMY_PAIRED_CONVERGENCE_20261119.md`): not formalized here.
- The symbols above are those of the merged Lean files `V166HolonomyPair` and `ReactiveHolonomyV166`;
  the correspondence with the printed display `eq:hol-det` of the 24 Nov 2026 `16.tex`
  (in particular `x = πa`, `c = cos 2πφ`) was not re-read in the source, which was not available to this
  run, and is to be confirmed.
- `cor:hol-eulerian` beyond the closed-form identities already in `ReactiveHolonomyV166`.
