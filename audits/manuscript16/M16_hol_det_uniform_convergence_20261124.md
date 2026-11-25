# M16 §14.5 `eq:hol-det`: local uniform convergence of the paired holonomy product — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/HolonomyUniformConvergence20261124.lean` (11 audited declarations).

## Starting point

`lean/Manuscript16/CERTIFICATION_SCOPE_20261117_V166_REACTIVE_HOLONOMY.md` lists for `eq:hol-det`
as remaining: "uniform convergence and Euler sine product applied to the circle spectrum". The Euler
evaluation for fixed parameters is in `main` (#596, `HolonomyEulerProduct20261124`), whose audit
records "Uniform convergence in `(a, φ)` on compact sets ... not formalized here".
`docs/manuscript16/V166_HOLONOMY_PAIRED_CONVERGENCE_20261119.md` gives the written argument ("for `a`
and `φ` varying in compact subsets of `a > 0` and `φ` real ... local uniform convergence and
nonvanishing"). No Lean statement with `TendstoUniformlyOn` or `TendstoLocallyUniformlyOn` exists in
`lean/Manuscript16`, and no open PR treats it (checked 24 Nov 2026, 22:00 UTC: the eight open PRs are
#587, #584, #582, #581, #565, #563 (M11–M14), #474 (shared Fredholm trace) and #394 (M11); none
touches `lean/Manuscript16`).

## What is proved

Parameters `p = (a, φ) ∈ ℝ × ℝ`, `posHalf = {p | 0 < p.1}`;
`pairedLimit p = a²(sin²(πφ) + sinh²(πa)) / ((φ²+a²) sinh²(πa))`.

| Declaration | Statement |
|---|---|
| `isOpen_posHalf` | `posHalf` is open |
| `continuous_pairDev`, `continuous_pairConstant` | `p ↦ pairRatio a φ (n+1) − 1` and `p ↦ pairConstant a φ` are continuous on `ℝ × ℝ` |
| `pairDev_uniform_bound` | for compact `K`: `∃ C ≥ 0, ∀ n, ∀ p ∈ K, |pairRatio a φ (n+1) − 1| ≤ C/(n+1)²` |
| `summable_inv_succ_sq` | `∑ₙ C/(n+1)² < ∞` |
| `paired_product_tendstoUniformlyOn` | **compact `K ⊆ posHalf`: `∏_{n=1}^{N} pairRatio a φ n → pairedLimit (a, φ)` uniformly on `K`** |
| `paired_product_tendstoLocallyUniformlyOn` | **the same convergence is locally uniform on `posHalf`** |
| `pairedLimit_pos` | `pairedLimit p > 0` for `p ∈ posHalf` (nonvanishing) |
| `pairedLimit_mul_eq` | `(φ²+a²)/a² · pairedLimit (a, φ) = productClosed (πa) (cos 2πφ)` for `a > 0` |
| `holonomy_det_tendstoUniformlyOn` | **compact `K ⊆ posHalf`: `((φ²+a²)/a²) ∏_{n=1}^{N} pairRatio a φ n → (cosh 2πa − cos 2πφ)/(cosh 2πa − 1)` uniformly on `K`** |
| `holonomy_det_tendstoLocallyUniformlyOn` | **the same convergence is locally uniform on `posHalf`** |

Together with `holonomy_det_limit_ge_one` (#596), the limit with the `n = 0` factor is `≥ 1`
on `posHalf`. The statements are `Filter` statements for the actual real functions of `(a, φ)`; no
finite grid, sampling or numerical surrogate is used.

Local check (pinned toolchain, 24 Nov 2026): `V166HolonomyPair`, `ReactiveHolonomyV166`,
`HolonomyEulerProduct20261124` and the new file compile with exit 0; the new file has no warning and
no error; its 11 declarations depend only on `propext`, `Classical.choice`, `Quot.sound`; the 29 axiom
reports of the three imported modules contain only these three. Local source SHA-256:
`bfa4821b40332f50a642ca4ae81eb0e22b848dbeca661b06e049f26612763491`. The certifying run is
`.github/workflows/m16-hol-det-uniform-convergence-20261124.yml` (exact-HEAD checkout, pinned
toolchain, compilation of the imported modules, `#print axioms` audit of 11/11 declarations and 29
imported reports, failure on any warning in the new file, artifacts).

## Published results cited, not re-proved

- Uniform Weierstrass test for products `∏ (1 + fₙ)` with `‖fₙ‖ ≤ uₙ` on a compact set,
  `∑ uₙ < ∞`, `fₙ` continuous: classical; used through Mathlib
  `Summable.hasProdUniformlyOn_nat_one_add`.
- Equivalence of locally uniform convergence on an open subset of a locally compact space with
  uniform convergence on its compact subsets: Mathlib `tendstoLocallyUniformlyOn_iff_forall_isCompact`.
- Euler's sine product: through the merged `HolonomyEulerProduct20261124` (Mathlib
  `Complex.tendsto_euler_sin_prod`).

## Not claimed

- That `∏ pairRatio` is the determinant of the holonomy operator on the circle spectrum (operator
  determinant, spectral theorem, trace-class membership): not formalized.
- Uniformity up to `a = 0` or for unbounded `φ`: not claimed (only compact subsets of `a > 0`).
- The correspondence of the symbols with the printed display `eq:hol-det` of the 24 Nov 2026 `16.tex`
  (in particular `x = πa`, `c = cos 2πφ`) was not re-read in the source, which was not available to this
  run, and is to be confirmed.
