# Manuscript 14.10 — Hermite–Lindemann integrated Lean certificate (EXPERIMENTAL)

**Verified on 4 November 2026.** This document reports a real, successful kernel check of the *sole research Theorem 11.1* of Manuscript 14.10, but **NOT** a replacement of the officially pinned Lean/Mathlib configuration.

## Reproducible checkpoint

- **GitHub Actions:** [#41813425159 — SUCCESS](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41813425159)
- **Verified repository commit:** `8086db2853bc5edcb586f53827aec5e55e985200`
- **Isolated branch:** `manuscript14-lindemann-pr28013-experiment-20261104`
- **Lean:** `leanprover/lean4:v4.36.0-rc2`
- **Experimental Mathlib:** `https://github.com/astrainfinita/mathlib4` at immutable commit `54fbfba6f39455b27daaff60830df6a627de8847`, the head of [upstream PR #28013](https://github.com/leanprover-community/mathlib4/pull/28013) at verification time.
- **Primary source:** `lean/SpecialImaginaryPoint/HermiteLindemannPrExperiment.lean`, using imported `transcendental_exp`.
- **Integrated final source:** `lean/SpecialImaginaryPoint/HermiteEulerianCompleteExperiment.lean`.
- **Supporting modules:** `ParryThresholds.lean`, `EulerianAnalyticBracket.lean`, `PeriodicOrbitAlgebraicity.lean`, `EulerianTranscendenceReduction.lean`.
- The GitHub Actions job compiled all these modules *together in the upgraded toolchain*; none of their imported previous results was assumed from a stale binary certificate.

## Formal mathematical content, fully kernel-checked in this experiment

1. `Manuscript14LindemannExperiment.exp_one_div_sqrt_two_transcendental`: `¬ IsAlgebraic ℚ (Real.exp (1 / Real.sqrt 2))` via Mathlib PR #28013's `transcendental_exp` and explicit ℤ-to-ℚ algebraic descent.
2. `Manuscript14LindemannExperiment.eulerian_companion_transcendental`: `¬ IsAlgebraic ℚ (Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2))`, using only algebraic closure and `cosh² = 1 + sinh²`.
3. `Manuscript14Section11.eulerian_14_10_theorem11_1_complete`: a *single unconditional Lean theorem* asserting:
   - the exact actual floor-based greedy prefix `1 0^30 1` for the Eulerian `x_E`;
   - existence and uniqueness of the relevant trinomial thresholds, with `β₃₂ < x_E < β₃₁`;
   - the strict 31st-iterate orbit-defect enclosure `0.000313240 < 1 - T_{x_E}^31(1) < 0.000313241`;
   - `T_{β₃₁}^31(1)=0` and left-hand limit `T_β^31(1)→1` as `β↑β₃₁`;
   - transcendence of `x_E`;
   - non-eventual periodicity of the actual greedy digit sequence.
4. The CI emitted **47 separate `#print axioms` checks** for source declarations across the imported and final modules, not 47 different original mathematical results.

**Exact final axiom audit from the verified CI:**
```
'Manuscript14Section11.eulerian_14_10_theorem11_1_complete'
depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorryAx` or `Lean.ofReduceBool`. No custom assumptions were introduced.

## Arb (independent numerical companion, unchanged)

The manuscript's dedicated 256-bit `python-flint==0.9.0` script has **26/26 SUCCESS** in [CI #41809760282](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809760282), including the printed seven-term `s₆` remainder enclosure, threshold signs, floor-block precritical inequalities and exact defect bounds. It is a separate, already verified numerical record; **not** a new Arb run in CI #41813425159.

## Critical qualification for publication / archiving

The upstream Mathlib PR #28013 is **unmerged**, and the experimental toolchain is newer than Manuscript 14's official pins. Therefore the experimental theorem is a genuine, reproducible Lean kernel certificate **conditional on that specific unmerged upstream source being available**, but it must not be described as part of the official `v4.35.0-rc3` / pinned Mathlib certification.

The project's official manuscript 14.10 PR #30 and `CERTIFICATION_LEDGER_v7.md` stay unchanged. Do not merge this experimental branch into PR #30 or `main` without a separate author decision and compatible Mathlib integration. V007, V097, manuscripts 11–13 and the PDF/TeX of 14.10 remain untouched.
