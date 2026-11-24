# M16/M17 exact-head audit — 24 Nov 2026

Scope: Manuscripts 16 and 17 and PRs #458, #459, #566, #567 only. Manuscripts 11–15 are not touched.

## Reference packages

| Package | SHA-256 |
|---|---|
| `Manuscript_16_20261124_EDITORIALE_EQUAZIONI_COMPLETE.zip` | `f85ef457f5ac5642b196a7f9a9ffbd9fcd854c1f3b33a06b03a4f53757892465` |
| `16.tex` | `289ad937a340feb70f6b9751006700eea2ee4219eaf8dc9f7b6758144fd3b108` |
| `Manuscript_17_20261124_EDITORIALE_EQUAZIONI_COMPLETE.zip` | `a9e6857871da9c0fee6b1af69e966e1db1979a26dfdf288b8953f644ac356c89` |
| `Cyclohedral.tex` | `5920a8886656b398afde714a25df662b50e4742420de18fcbd5d78eb9f1e1c79` |

Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`, python-flint `0.9.0`.

## Pull requests

| PR | Failing head | GitHub failure (job) | Cause | Fix commit | Change |
|---|---|---|---|---|---|
| #458 | `667d6c0764897c1e94a18f8162183858069ae093` | 135541359352 | `NormedField ℂ` not synthesized: only `Mathlib.Analysis.Normed.Operator.Compact.Basic` imported | `f678d81ef5041a39ec9f2fa8f3f85980ec6cca83` | `import Mathlib.Analysis.Complex.Basic`; docstring |
| #459 | `2094b78591f0cd88682d59dfee7d765002bbb2e6` | 135542411127 | `finiteIndex` depends on noncomputable `finrank` | `661d3247914939520faa56161a1e865c1d5b29f8` | `noncomputable def`; docstring |
| #566 | `f401ac926c9629800e8faeaaa7c308137a973c99` | 138393702201 | `null_curve_tangent`: unsolved function-equality goal, hence `sorryAx` | `10c6efabd27c85e37bcf818956b9988d468f2b2e` | proof of the `convert` side goal only |
| #567 | `38914fb8ce77893da12701314841edf697de715a` | — (success, merged 24 Nov 2026 11:33 UTC as `75a664b0`) | — | — | — |

No statement was changed. Before pushing, all 24 declarations were recompiled locally on the pinned toolchain; every one depends only on `propext`, `Classical.choice`, `Quot.sound`. The GitHub runs on the new heads are the certifying runs.

## Fredholm obligations already in `main`

`lean/SharedCore/FredholmAtkinson.lean` (PR #469, merged 19 Nov 2026) was recompiled locally with standard axioms. It already proves Atkinson's criterion in both directions (`isFredholm_iff_compact_parametrix`), `isFredholm_add_compact`, `index_add_compact` (`ind(T+K) = ind T` for every Fredholm `T` and compact `K`, without any smallness or normality hypothesis) and `compact_shift_isFredholm_index_zero`. The docstrings of #458 and #459 no longer describe index invariance as open.

## M16 `cor:feff-maxwell`, `eq:feff-det`

Decision of the scientific lead (24 Nov 2026): the unitary invariance of `det_p` on `S_p` is a published result cited from Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS 2005 (`Simon2005` in M16), not a result of the manuscript. Since `eq:feff-det` is exactly that invariance applied to the unitary `P` of `eq:feff-P`, a Lean statement taking it as a premise would restate its own hypothesis; it is therefore recorded as a published result cited and is not an open Lean obligation. The finite-dimensional identity is certified in `lean/Manuscript16/FeffermanDetConjugacy20261124.lean` (#567). The precise theorem of Simon 2005 that is used is still to be located in the book.

## Status register

| Obligation | Status |
|---|---|
| #458 compact-parametrix defects (normed spaces) | CI on `f678d81e` pending |
| #459 finite Schur block index; affine norm path | CI on `661d3247` pending |
| #566 M17 coordinate tangent pullback (`m17-feff-metric-proof`, `m17-feff-critical-metric`, `m17-feff-Dirichlet-energy`) | CI on `10c6efab` pending; FORMALIZZAZIONE PARZIALE (coordinate level: no smooth quotient, intrinsic Laplace–Beltrami or manifold integration) |
| `ind(T+K) = ind T` | LEAN 4 CERTIFICATO, INTEGRATO (`SharedCore.FredholmAtkinson.index_add_compact`) |
| M16 `eq:feff-det`, finite dimension | LEAN 4 CERTIFICATO, INTEGRATO (#567) |
| M16 `eq:feff-det` on `S_p` | published result cited (Simon 2005) |
| M16 `thm:dirac-maxwell-obstruction-164` (i)–(ii) | APERTO as an assembled statement: `V165GraphSchur.typed_factorization` assumes `L : D ≃L X`; transfer of Fredholmness/index through the shears and `diag(F, L)`, and the construction of `L` from `L₀`, are missing |
| M17 L₈(1,χ₂), Area_Φ at 30,000 places | ARB CERTIFICATO (#553); certificate now persisted, see below |

## M17 numerical evidence

- `certificates/M17_cassini_area_L8_30000_decimal_certificate_20261124.json` (SHA-256 `cff42e7fc7fbe8435e1306421cd12e11f26da45f2de0622ce8adc37fe283fd7a`) and its log: output of the unchanged `numerics/arb/m17_cassini_area_30000_decimal.py` (120,000 working bits; verified relative accuracy 119,997 and 119,996 bits; strict half-ulp rounding cell; historical 20,000-place SHA-256 regression passed). Before this commit the certificate existed only as an expiring CI artifact. The workflow `m17-arb-persistence-independent-quadrature-20261124.yml` re-runs the script at the exact PR head and requires byte identity with the persisted JSON.
- `numerics/arb/m17_independent_quadrature.py`: rigorous Arb quadrature (`acb.integral`) of `∫₀¹ (1−x²)/(1+x⁴) dx` (`eq:m17-L8-integral`) and `2π ∫₀¹ ν²/(2−ν²)² dν` (`eq:m17-area-integration`), plus `atanh(1/√2)/√2`, compared with the closed forms. At 10,000 bits all balls overlap, with verified relative accuracy ≥ 9,988 bits. This route does not share the logarithmic closed form used by the 30,000-place script; it does not replace the analytic proofs in the manuscript.
- Exact symbolic checks (SymPy): `eq:m17-feff-hemisphere`, `eq:m17-laplacian`, both forms of `eq:m17-curvature`, the primitives in `eq:m17-area-integration` and `eq:m17-L8-integral`.

## Notes for the manuscript text (not modified)

- M17 Data Availability still cites commit `65ba6d13`.
- M17 lines 1312 and 1315 use `\operatorname{artanh}`.
