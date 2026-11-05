# Manuscript 14.9 — Certification ledger v5 (Lean 4 / Arb)

**Verified / updated:** 4 November 2026 (UTC).  
**Scope:** autonomous Manuscript 14.9, particularly its new Section 11, *Eulerian Fourier Profiles and Parry Thresholds in Symbolic Dynamics*.  
**Branch:** `manuscript14-section11-parry-cert-20261103`, based on `special-point-i-sqrt2-cert-20261103`.  
**Pull request:** [#30](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/30) (**DRAFT — DO NOT MERGE**).

This v5 ledger **supersedes v4 for the status report only**; v4 is retained unchanged and describes the older manuscript 14.1. It does not imply that the paper's entire 14.9 statement inventory has been re-audited. Preserve the separation of manuscripts 11–14, V007, V097 and main.

## 1. Exact verified CI checkpoints

| Scope | Last SUCCESS run | Source-tested commit | Lean kernel-audited declarations | Arb / exact checks |
|---|---|---|---:|---:|
| Existing special-point theory (Sections 1–10 as applicable) | [#41723312459](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723312459) | `66351b9dcf02b3a2b5f89cbcb340e81a886ef50c` | **25** | **37 PASS** |
| New Section 11 Parry thresholds | [#41727177204](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41727177204) | `3d6f049416c7d3929425061b0402563b00d9d9ce` | **9** | **16 PASS** |
| **Aggregate across disjoint modules/scripts** | Two SUCCESS checkpoints | See above | **34 declarations** | **53 checks** |

**Critical counting rule:** Lean declarations, Arb tests, and printed theorems/propositions are three different units. The two counts (34 and 53) **do not mean 34 complete paper theorems or 53 mathematical theorems certified**. The script checks are logically bounded to their explicit claims; whole-operator and transcendence statements are not proved by numerical evaluations.

The latest Section 11 source-file blob SHAs are `c965bf14c49a65bf0d7f634fbf095fe79ca177ac` for `ParryThresholds.lean` and `459012773e7731512bf096932f8ff06dbd59627e` for `manuscript14_section11_arb.py`. Later changes to Markdown documentation were not part of CI paths and did not modify these tested proof sources.

## 2. Lean 4 status — exact declaration audit

**Toolchain:** `leanprover/lean4:v4.35.0-rc3`; Mathlib at `0272bbe1c093d038d7257ab15306abd58245f9ff`.

**Prior special-point branch: 25 declarations from four modules.**
- `DenominatorRecurrence.lean` — 4: exact factorial denominator recurrence and initial values.
- `FormalBorel.lean` — 5: scalar Borel coefficient and algebraic identities.
- `FormalBorelComplex.lean` — 6: exact identity on `PowerSeries ℂ`, formal differential operations.
- `BorelAnalyticConvergence.lean` — **10 additional declarations**, all verified on [#41723312459](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723312459):
  `eulerianEntireSeries_summable`;
  `eulerianEntireSeries_hasSum`;
  `eulerianEntireSeries_hasFPowerSeriesAt_zero`;
  `eulerianEntireSeries_analyticAt_zero`;
  `eulerianEntireSeries_radius_top`;
  `eulerianEntireSeries_hasFPowerSeriesOnBall`;
  `eulerianEntireSeries_analyticAt`;
  `eulerianEntireCoeff_recurrence`;
  `eulerianEntireSeries_zero`;
  `eulerianEntireSeries_deriv_zero`.
  These certify a genuinely entire function
  `F(t)=Σ_{n≥0}4^n t^n/(2n+1)!`, rather than merely formal coefficients.
  The full analytic ODE and its identification with all printed analytic operator statements remain separately unproved.

**New Section 11 branch: 9 kernel-certified declarations in `ParryThresholds.lean`:**
1. `f32_left_positive`: exact rational sign for the 32nd trinomial.
2. `f31_right_negative`: exact rational sign for the 31st trinomial.
3. `delta_left_exact`: rational lower comparison for orbit defect.
4. `delta_right_exact`: rational upper comparison for orbit defect.
5. `strict_parry_return`: universal real-interval transfer to `β^30(β−1)<1<β^31(β−1)`.
6. `parry31_two_digit_identity`: `β^31−β^30−1=0` implies `1=β⁻¹+β⁻³¹` when `β≠0`.
7. `precritical_zero_digit_bounds`: inequalities for all `k≤30`.
8. `next_one_digit_bounds`: next greedy remainder lies strictly between 1 and 2.
9. `eulerian_initial_greedy_block`: combines the preceding interval-conditional inequalities.

The latest [#41727177204](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41727177204) Lean log explicitly lists `#print axioms` for **all nine** declarations. The only dependencies are `propext`, `Classical.choice` and `Quot.sound` (possibly subsets thereof): **no `sorryAx`, no `Lean.ofReduceBool`**.

**Important scope limitation:** the nine theorems are real inequalities / rational identities, conditional on the numerical bracket. This file does not yet formalize the actual floor-based greedy-digit recursion and does not define `x_E` within Lean as a hyperbolic function. Their application to `x_E` has been independently checked with exact rationals and Arb but is **not a single Lean theorem** end-to-end.

## 3. Arb / rational certificate status

**Configuration:** `python-flint==0.9.0`, 256-bit Arb real balls plus Python `fractions.Fraction`.

**Pre-existing scalar script** `numerics/arb/special_point_i_sqrt2_arb.py`, [CI #41723312459](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723312459): **37 PASS**. It checks 10 scalar approximations at two points and rounding to 50 significant digits, positive Taylor remainder, coefficients, special-value bounds, and proximity of `j(i/√2)` and `j(i√2)` to 8000. Arb overlap/accuracy tests do *not* independently prove an exact modular identity or operator-trace identity.

**Section 11 script** `numerics/arb/manuscript14_section11_arb.py`, [CI #41727177204](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41727177204): **16 PASS**. It proves rigorous Taylor enclosures for
`x_E = √2 sinh(1/√2)`, rational isolation of roots of `F_n(x)=x^(n−1)(x−1)−1`,
`β_32 < x_E < β_31`, and a certified strict defect
`0.000313240 < 1−x_E^30(x_E−1) < 0.000313241`.
The log reports
`x_E = [1.0854416412726070018696230810771799943362362464372659282079534489 +/- 1.15e-65]`
and defect
`[0.00031324061531572976451633905251151178299215998503599171620515735142 +/- 2.08e-69]`.

## 4. Detailed verification boundary — NOT fully Lean-certified

- The exact *analytic identity* `x_E=√2 sinh(1/√2)` linked to the original Fourier transform in manuscript 14.9, including the sine/sinh and exponential-integral bridges.
- The complete floor-based `T_β` digit recursion, starting from 1, including the formal equivalence between digit inequalities and the sequence `1 0^30 1 ...`.
- Transcendence of `x_E` via Lindemann and consequent non-eventual-periodicity of its greedy digit expansion.
- The genuine Perron–Frobenius transfer-operator identity, invariance/normalization of Parry's density, and the Fourier-sinc representation with all exchange-of-limit justifications.
- Any new spectral equivalence, the full Fredholm/Dirichlet determinant and domain-aware operator assertions not already inherited exactly from manuscripts 11–13.
- Unproved Mersenne-index mechanism (31=2^5−1 is an elementary identity, **not** an established dynamical explanation).

**The older v4 report's `0/20` count relates to its 20 fully printed manuscript-14.1 statements at that checkpoint.** It must not be mechanically transferred to the expanded 14.9 theorem inventory; no exhaustive statement-by-statement audit of the expanded typeset 14.9 was performed in this v5 status update.

## 5. Priority / publishing constraints

Research audit: [`research/Manuscript14_SECTION11_PRIORITY_AUDIT.md`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/manuscript14-section11-parry-cert-20261103/research/Manuscript14_SECTION11_PRIORITY_AUDIT.md).
The family `x^n−x^(n−1)−1` and finite greedy words, and Parry's invariant-density construction, are known: cite Hare–Hichri (2026), Cornean–Herbst–Sørensen (2026), and Parry (1960). The specific Eulerian bracketing / orbit defect may be a new specialization, but exhaustive priority has not been established. Verger-Gaugry's Salem bound remains a claim whose general validity should not be presumed.

**No automatic merging, no modification to the manuscript PDF/TeX, no updates to V007/V097/main.** The present record reflects the **latest verified successful CI**, not an unexecuted future task.
