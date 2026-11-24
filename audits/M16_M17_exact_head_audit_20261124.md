# M16/M17 exact-head audit — 24 Nov 2026

Scope: Manuscripts 16 and 17 and PRs #458, #459, #566, #567, #576, #585, #588, #589, #592, #593, #594 only. Manuscripts 11–15 are not touched.

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
| #576 | `be873bda4fc77f64e60ce7fcb75b9d2298b227aa` | — (exact-head job 138465626693 success; merged 24 Nov 2026 13:30 UTC as `a67953ca`) | — | — | — |
| #585 | `76de0e10893c5e1391a1de54b9f89b83df49612a` | — (exact-head job 138502217880 success: 18 declarations and 46 imported axiom reports, standard axioms only; merged 24 Nov 2026 14:10 UTC as `9c605296`) | — | — | — |
| #588 | `26feb5138136e592551caf480c471b08d5dec239` | — (exact-head job 138585661565 success; merged 24 Nov 2026 20:29 UTC as `ef3ce900`) | — | — | — |
| #589 | `3bcc3980d43af708958559c459e0781c5aef0271` | — (exact-head jobs 138629459202, 138629456454 success; head reached `main` through the #594 merge `9f949f04`, 24 Nov 2026 20:30 UTC) | — | — | — |
| #594 | `b2dba1339fd15196c3c6cb64e899ed41ae47fe56` | — (exact-head jobs 138740702462, 138740701048, 138740700805 success; merged 24 Nov 2026 20:30 UTC as `9f949f04`) | — | — | — |
| #593 | `5c36eba71306420fc58df71613fe51f1f3b5c42c` | — (exact-head job 138699649288 `area-integration` success, job 138699646173 M11 suite success; merged 24 Nov 2026 20:31 UTC as `1bbc0bfa`) | — | — | — |
| #592 | `ed0bcdc1567043521a4cd14db37acf2a70ba326d` | — (exact-head jobs 138663895750, 138663893085 success; merged 24 Nov 2026 20:31 UTC as `5f3cdc87`) | — | — | — |

No statement was changed. Before pushing, all 24 declarations were recompiled locally on the pinned toolchain; every one depends only on `propext`, `Classical.choice`, `Quot.sound`. The GitHub runs on the new heads are the certifying runs.

## Fredholm obligations already in `main`

`lean/SharedCore/FredholmAtkinson.lean` (PR #469, merged 19 Nov 2026) was recompiled locally with standard axioms. It already proves Atkinson's criterion in both directions (`isFredholm_iff_compact_parametrix`), `isFredholm_add_compact`, `index_add_compact` (`ind(T+K) = ind T` for every Fredholm `T` and compact `K`, without any smallness or normality hypothesis) and `compact_shift_isFredholm_index_zero`. The docstrings of #458 and #459 no longer describe index invariance as open.

## M16 `cor:feff-maxwell`, `eq:feff-det`

Decision of the scientific lead (24 Nov 2026): the unitary invariance of `det_p` on `S_p` is a published result cited from Simon, *Trace Ideals and Their Applications*, 2nd ed., AMS 2005 (`Simon2005` in M16), not a result of the manuscript. Since `eq:feff-det` is exactly that invariance applied to the unitary `P` of `eq:feff-P`, a Lean statement taking it as a premise would restate its own hypothesis; it is therefore recorded as a published result cited and is not an open Lean obligation. The finite-dimensional identity is certified in `lean/Manuscript16/FeffermanDetConjugacy20261124.lean` (#567). The precise theorem of Simon 2005 that is used is still to be located in the book.

## Status register

| Obligation | Status |
|---|---|
| #458 compact-parametrix defects (normed spaces) | INTEGRATO (`8b9217cb`, 24 Nov 2026 11:50 UTC) |
| #459 finite Schur block index; affine norm path | INTEGRATO (`3371f94e`, 24 Nov 2026 11:51 UTC) |
| #566 M17 coordinate tangent pullback (`m17-feff-metric-proof`, `m17-feff-critical-metric`, `m17-feff-Dirichlet-energy`) | INTEGRATO (`813e9a87`, 24 Nov 2026 11:51 UTC); FORMALIZZAZIONE PARZIALE (coordinate level: no smooth quotient, intrinsic Laplace–Beltrami or manifold integration) |
| `ind(T+K) = ind T` | LEAN 4 CERTIFICATO, INTEGRATO (`SharedCore.FredholmAtkinson.index_add_compact`) |
| M16 `eq:feff-det`, finite dimension | LEAN 4 CERTIFICATO, INTEGRATO (#567) |
| M16 `eq:feff-det` on `S_p` | published result cited (Simon 2005) |
| M16 `thm:dirac-maxwell-obstruction-164` (i)–(ii) | Abstract typed form in `lean/Manuscript16/DiracMaxwellObstructionIndex20261124.lean`, INTEGRATO (#576, `a67953ca`; exact-head CI job 138465626693 success on `be873bda`): `𝒜` Fredholm iff `A_P` Fredholm and `ind 𝒜 = ind A_P`, with Mathlib `IsFredholm`/`index`, under the premises `L : D ≃L X` and `B L⁻¹ C` compact. Graph-space form for an abstract closed bijective `L₀` with compact `R₀`, `‖R₀‖ ≤ 2/3`, `‖E‖ < 3/2`: `lean/Manuscript16/DiracMaxwellGraphSpace20261124.lean`, INTEGRATO (#585, `9c605296`; exact-head CI job 138502217880 success on `76de0e10`; see `audits/manuscript16/M16_dirac_maxwell_graph_space_20261124.md`). With #576 and #585 the abstract obligation (diagonal lemma `diag(F, L) = F.prodMap L`, `ker = ker F × 0`, `coker ≅ P / range F`, assembly through `typed_factorization`, `IsFredholm.index_comp`, `index_add_compact`) is closed and must not be re-proved. For the coefficient-space realization of `L₀ = W_R ⊕ D₃` on `ℓ²(MixedIndex, ℂ)` the four premises (closed, bijective, `‖R₀‖ = 2/3`, `R₀` compact) are discharged in `lean/Manuscript16/DiracMaxwellCoefficientModel20261124.lean`, INTEGRATO (#588, `ef3ce900`; see `audits/manuscript16/M16_dirac_maxwell_coefficient_model_20261124.md`): `coefficientModel_isFredholm_iff_and_index_eq` has no premise on `L₀`. The unitary identification of `ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)` is a published input, not formalized; no geometric statement on `S³` is derived |
| M17 L₈(1,χ₂), Area_Φ at 30,000 places | ARB CERTIFICATO (#553); certificate now persisted, see below |
| M16 `eq:mixed-schatten-164`, sequence level | LEAN 4 CERTIFICATO, INTEGRATO (#589, via `9f949f04`): `mixedWeight_summable_iff`, `∑ᵢ |wᵢ|ᵖ < ∞ ⇔ p > 3` for every real `p`; `L0_resolvent_weights_memℓp_iff`. Operator form `L₀⁻¹ ∈ S_p ⇔ p > 3`: published inputs cited (Simon 2005, Ch. 2: `diag(w) ∈ S_p ⇔ w ∈ ℓᵖ`, ideal property), not a Lean theorem (no Schatten classes in Mathlib at the pinned commit) |
| M16 `eq:mixed-lower-series-164`, `eq:mixed-upper-series-164` | LEAN 4 CERTIFICATO, INTEGRATO (#594, `9f949f04`): `lowerSeries_summable_iff`, `maxwell_summable_iff`, `maxwellWeight_memℓp_iff`, `upperSeries_le` on the actual index type `MaxwellIndex`. Correspondence with the printed displays of `16.tex` still to be confirmed against the source (not available to the certifying run) |
| M16 `eq:mixed-det4-criterion-164`, operator part | LEAN 4 CERTIFICATO, INTEGRATO (#592, `5f3cdc87`): `coefficientModel_resonant_invertibility`, for every `μ ≠ 0`: `𝒜(μ)` bijective ⇔ injective ⇔ `I − μ⁻¹K` bijective ⇔ `μ ∉ σ(K)`, eigenspace finite-dimensional, `K = B L⁻¹ C` compact. The `det₄` step (`I + T` invertible ⇔ `det₄(I + T) ≠ 0`, `T ∈ S₄`) and `K ∈ S₄`: published inputs (Simon 2005, Ch. 9 and Ch. 2), not Lean theorems |
| M16 `eq:mixed-det4-164` and `det₄` step of `eq:mixed-det4-criterion-164` | DECISIONE DEL RESPONSABILE RICHIESTA: published result cited (Simon 2005), as for `eq:feff-det`, or open Lean obligation (construction of `S₄` and `det₄`). Precise theorem numbers in Simon 2005 still to be located |
| M16 discreteness of `σ(K) \ {0}` | Riesz–Schauder theory, classical; not formalized |
| M17 `eq:m17-area-integration` | LEAN 4 CERTIFICATO, INTEGRATO (#593, `1bbc0bfa`): `area_integration`, `2π ∫₀¹ ν²/(2−ν²)² dν = π(1 − log(1+√2)/√2)` as a Mathlib interval integral. Not claimed: that the integral is the area of the critical Cassini lobe (metric integration, geometric), `log(1+√2)/√2 = L₈(1, χ₂)` (Dirichlet, cited) |

## Post-merge consistency of `main` (#588, #589, #592, #593, #594)

Checked 24 Nov 2026 on `main` = `9e762b4b9dc72ad0cc2f5d5be66fa741249ba493`. The seven files certified by these PRs are byte-identical in `main` and at their certifying heads (SHA-256):

| File | Certifying head | SHA-256 |
|---|---|---|
| `lean/Manuscript16/DiracMaxwellCoefficientModel20261124.lean` | #588 `26feb513` | `449afea7fadc8e610f0c3bbbeb1f4c9af6d193ec10a0308210a34ec88aa000e4` |
| `lean/Manuscript16/V166L2SpectralInverse.lean` | #588 `26feb513` | `f7fdb0b544f7bb5c9be5ad83885d6c3b7c4ac518f2a4ee2dcd6c25189d84cab5` |
| `lean/Manuscript16/V166SpectralCutoffs.lean` | #588 `26feb513` | `47fd91b90ca0a75336a83821cab632f0c0495f99e2efe8b79a44d98aac827634` |
| `lean/Manuscript16/DiracMaxwellSchattenThreshold20261124.lean` | #589 `3bcc3980` | `71335d9d9d9f8b67de5b17af4a0fbfa699787b668bae70204f19d8bfff59d6b0` |
| `lean/Manuscript16/MaxwellLowerUpperSeries20261124.lean` | #594 `b2dba133` | `ac9cd6600cb801258502ce06d8f804bb42cdc38bce690c3db6f556078e93d6b8` |
| `lean/Manuscript16/DiracMaxwellResonantInvertibility20261124.lean` | #592 `ed0bcdc1` | `7f11155a0707aad3eecd4a254ebe7ffc1a70972fe7a4267db47acdadca4a9f1f` |
| `lean/EulerianCert/CassiniAreaIntegral20261124.lean` | #593 `5c36eba7` | `772e441955a1dbfe6dca4c2479cd5ef4997bbc400cc68cc1989f652cacecdc0b` |

Between each certifying head and `main`, `git diff` restricted to `lean/SharedCore`, `lean/Manuscript16`, the M17 file, `lean/lakefile.toml` and `lean/lean-toolchain` shows only added files (the other PRs of this group); no imported module, the toolchain or the Mathlib pin changed. The PR-triggered workflows do not run on pushes to `main`; the combined state is re-audited by `.github/workflows/m16-m17-post-merge-reaudit-20261124.yml` (exact-HEAD checkout, ancestry check of the four merge commits, hash check of the seven files, compilation of the 15 modules in dependency order on the pinned toolchain, `#print axioms` audit of all 170 reports, failure on any warning in the five new modules, artifacts). That run is the certifying run for the combined state.

The `push` runs of `.github/workflows/m11-dk-20000-decimal-production.yml` on `main` fail on every merge, including those of this group; that workflow belongs to Manuscript 11 and is outside the scope of this register.

## M17 numerical evidence

- `certificates/M17_cassini_area_L8_30000_decimal_certificate_20261124.json` (SHA-256 `cff42e7fc7fbe8435e1306421cd12e11f26da45f2de0622ce8adc37fe283fd7a`) and its log: output of the unchanged `numerics/arb/m17_cassini_area_30000_decimal.py` (120,000 working bits; verified relative accuracy 119,997 and 119,996 bits; strict half-ulp rounding cell; historical 20,000-place SHA-256 regression passed). Before this commit the certificate existed only as an expiring CI artifact. The workflow `m17-arb-persistence-independent-quadrature-20261124.yml` re-runs the script at the exact PR head and requires byte identity with the persisted JSON.
- `numerics/arb/m17_independent_quadrature.py`: rigorous Arb quadrature (`acb.integral`) of `∫₀¹ (1−x²)/(1+x⁴) dx` (`eq:m17-L8-integral`) and `2π ∫₀¹ ν²/(2−ν²)² dν` (`eq:m17-area-integration`), plus `atanh(1/√2)/√2`, compared with the closed forms. At 10,000 bits all balls overlap, with verified relative accuracy ≥ 9,988 bits. This route does not share the logarithmic closed form used by the 30,000-place script; it does not replace the analytic proofs in the manuscript.
- Exact symbolic checks (SymPy): `eq:m17-feff-hemisphere`, `eq:m17-laplacian`, both forms of `eq:m17-curvature`, the primitives in `eq:m17-area-integration` and `eq:m17-L8-integral`.

## Notes for the manuscript text (not modified)

- M17 Data Availability still cites commit `65ba6d13`.
- M17 lines 1312 and 1315 use `\operatorname{artanh}`.
