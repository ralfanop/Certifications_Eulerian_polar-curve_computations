# Manuscript 15 — complete theorem-level Lean/Arb coverage matrix (revision e)

**Manuscript:** `Manuscript15_Revision_20261111e` (11 November 2026, 23 pages).
**Repository:** `ralfanop/Certifications_Eulerian_polar-curve_computations`.
**Status convention:** `kernel CERTIFIED` only after a successful exact-source run with #print axioms and permitted standard axioms; `Arb CERTIFIED` only for a *specific defined numerical expression* with a successful outward-enclosure check. A prose analytic proof is not automatically a formal proof.

| # | Manuscript result | Relevant source | Lean kernel coverage | Quantitative coverage | Remaining obligations |
|---:|---|---|---|---|---|
| 1 | Exact cycloidal reconstruction | Theorem 2.1, `thm:reconstruction` | X, Y, and kinematic identity kernel-checked in PR #112 | None required for functional identity | General library connection and numerical derivative/speed derivations |
| 2 | Speed and curvature realizations | `prop:curvature` | Reconstruction algebra only | None needed | Full differential/curvature theorem, cusp exclusions |
| 3 | Exact cycloidal–Fredholm–Langevin identity | `thm:fredholm` | Independent genuine universal Dirichlet Fredholm bridge, PRs #151, #159; needs declaration-level equivalence audit | Specializations numerically covered by Arb #179 | Exact translation of all displayed formulas and operator hypotheses |
| 4 | Special imaginary points | `cor:special` | Existing analytic/spectral dependencies; not counted as full M15 corollary | r_E(i/√2), r_E(i√2): Arb #179 | Formal complete corollary and branch conventions |
| 5 | Conformal Cayley half-angle chart | `prop:conformal` | Not certified in M15 | None | Explicit chart definitions, inverses and null-cone geometry |
| 6 | W₁ Lipschitz stability | `thm:wasserstein` | Abstract X and Y estimates submitted in PR #187 (CI pending); not full W₁ statement | No numeric values | Formal characteristic-function coupling / W₁ definition; compact-interval continuity |
| 7 | Rigidity of centred uniform law | `thm:rigidity` | `CoefficientRule` and its uniqueness kernel-checked (#112); c1–c7 kernel-checked (#115, #181) | No irrational constants required | Derive recurrence from analytic entire characteristic function; uniqueness of the measure |
| 8 | Exact leading cusp invariant | `prop:cusp` | Conditional leading algebra checked (#112) | None | Probability-law small-t expansion, rigorous limit |
| 9 | Compatibility and injectivity | `prop:compatibility` | Exact function-level compatibility, inverse and injectivity candidates PR #187 | No numerical values | Exact-head CI; measure uniqueness from characteristic function |
| 10 | Fourth-moment cusp expansion | `prop:cusp-fourth` | Arithmetic core PR #188 candidate | Exact rational moments; Arb unnecessary | Taylor remainder and quotient asymptotics |
| 11 | Universal leading cusp curvature | `prop:cusp-curvature` | No complete M15 formalization | None | Differentiation of asymptotics, curvature limit with sign |
| 12 | Convolution cusp / endpoint classification | `thm:convolutions` | Algebraic coefficient consequences PR #188 candidate | Exact integers/rationals; Arb unnecessary | rE^M derivatives at 2π; endpoint regularity; full cusp limit |
| 13 | Terminal contact order identifies convolution order | `cor:terminal-contact` | Not certified | None | Local analytic inversion, order-of-zero and derivative jet |
| 14 | Quadratic cusp correction for uniform sums | `cor:hierarchy-fourth` | Explicit fourth-moment and correction identities PR #188 candidate | Exact rational formulas | Independent uniform variables moment theorem and O(t⁴) remainder |

## Exact numerical layer

**PR #179, successful exact-source job:** [GitHub Actions #43080355596](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43080355596).
At `ctx.prec=10000`, all **14** evaluated nonzero real expressions achieved **9996–9998 certified relative bits**, strictly exceeding the **8182-bit** target. The Figure 1 annotation `α₃ ≈ 53.1301023542°` additionally passed the rounding-cell test. These are **certificates of the evaluated expressions only**, not of the asserted geometric or operator-theoretic interpretations.

## Formal proof semantics

`coefficientRule_c_four`–`coefficientRule_c_seven` in PR #181 passed exact-source [GitHub Actions #43080899625](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43080899625). They certify rational consequences conditional on `CoefficientRule`, **not** the proof that a probability law satisfying the kinematic identity must meet that rule.

## Additional non-theorem proof obligations

The numbered identities on area, Eulerian histogram, Plouffe/Sprugnoli inverse-binomial series, cone chart, endpoint order, higher derivatives, inverse moment extraction and physical research delimitations must be tracked at individual equation level. This matrix is an inventory of all **14 named theorem/proposition/corollary environments**, not an assertion that every mathematical statement is already formalized.

**Policy:** no changes to Manuscripts 11–14, V007 or V097; no unauthorized merges. Update this ledger only when CI outputs and the actual source declaration support an upgrade.


## Subsequent November 11 proof tracks

- PR #181: Lean coefficients c4–c7, exact-source kernel SUCCESS.
- PR #188: exact fourth-moment/cusp arithmetic, exact-source kernel SUCCESS.
- PR #202: exact integer mass/positivity/symmetry for every Eulerian profile n=3,…,7002 plus eight 10000-bit Arb peaks, exact-source SUCCESS (9998 certified relative bits).
- PRs #187, #191, #193, #200, #203, #204, #206, #208, #209: independent draft statements and workflows; CI results must be inspected before marking their declarations certified.

This appendix reports the verified state at its creation; consult the actual PR exact-head CI for later updates. In particular the nominal 10000-bit work precision is not itself an accuracy certificate.
