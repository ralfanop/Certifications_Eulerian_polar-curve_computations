# M17 `thm:m17-curvature-area`, `eq:m17-area-integration`: Lean 4 proof of the area integral — 24 Nov 2026

Scope: Manuscript 17 (`Cyclohedral.tex`) only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/EulerianCert/CassiniAreaIntegral20261124.lean` (13 audited declarations).

## Starting point

`eq:m17-area-integration`, as recorded in `numerics/arb/m17_independent_quadrature.py` and in
`certificates/M17_cassini_area_L8_30000_decimal_certificate_20261124.json`:

  2π ∫₀¹ ν² / (2 − ν²)² dν = π (1 − log(1 + √2) / √2).

Until now this identity was certified numerically (Arb closed form at 30,000 places, #553; independent
Arb quadrature at 10,000 bits) and its primitive symbolically (SymPy). The certificate states that it is
"not a proof of metric integration or L-series identity". No Lean statement about this integral existed
in `main` or in any open PR (checked 24 Nov 2026, 18:52 UTC).

## What is proved

| Declaration | Statement |
|---|---|
| `sqrt2_sq`, `one_lt_sqrt2`, `sqrt2_pos` | `(√2)² = 2`, `1 < √2`, `0 < √2` |
| `chart_factors_pos` | for `0 ≤ ν ≤ 1`: `√2 + ν > 0`, `√2 − ν > 0`, `2 − ν² > 0` |
| `hasDerivAt_areaPrimitive` | for `0 ≤ ν ≤ 1`, `F(ν) = ν / (2(2 − ν²)) − (log(√2 + ν) − log(√2 − ν)) / (4√2)` has derivative `ν² / (2 − ν²)²` |
| `areaDensity_intervalIntegrable` | `ν² / (2 − ν²)²` is interval integrable on `[0, 1]` |
| `areaPrimitive_zero`, `areaPrimitive_one` | `F(0) = 0`, `F(1) = 1/2 − log(1 + √2) / (2√2)` |
| `log_sqrt_two_sub_one` | `log(√2 − 1) = −log(1 + √2)` |
| `areaDensity_integral` | `∫₀¹ ν² / (2 − ν²)² dν = 1/2 − log(1 + √2) / (2√2)` (Mathlib interval integral, fundamental theorem of calculus) |
| `area_integration` | **`2π ∫₀¹ ν² / (2 − ν²)² dν = π (1 − log(1 + √2) / √2)`** |
| `log_one_add_sqrt_two_div_lt_one`, `area_value_pos` | `log(1 + √2) / √2 < 1`, hence the value is `> 0` |

The integral is Mathlib's interval integral of the actual real function; no finite-dimensional or
numerical surrogate is used.

Local check (pinned toolchain): exit 0, no warning and no error; all 13 declarations depend only on
`propext`, `Classical.choice`, `Quot.sound`. Source SHA-256:
`772e441955a1dbfe6dca4c2479cd5ef4997bbc400cc68cc1989f652cacecdc0b`. Numerical cross-check of the
closed form against the persisted 30,000-place certificate: `1.18367281763351…` in both.
Certifying run: `.github/workflows/m17-cassini-area-integration-lean-20261124.yml` (exact-HEAD checkout,
pinned toolchain, `#print axioms` audit of 13/13 declarations, failure on any warning, artifacts).

## Not claimed

- That this integral is the area of the critical Cassini lobe for the Fefferman metric. That step is
  metric integration on the surface, a geometric statement; it is not formalized (see also #566: no
  smooth quotient, intrinsic Laplace–Beltrami or manifold integration).
- `log(1 + √2) / √2 = L₈(1, χ₂)`: classical value of a Dirichlet L-series (Dirichlet), a published
  result cited, not formalized.
- The Gauss-curvature statements of `thm:m17-curvature-area` beyond the algebraic identities already
  in `CyclohedralFeffermanCurvature20261123.lean`.
