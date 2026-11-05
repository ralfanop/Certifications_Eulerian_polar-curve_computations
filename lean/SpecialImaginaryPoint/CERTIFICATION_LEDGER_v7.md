# Manuscript 14.10 — Lean 4 / Arb certification register v7

**Date:** 4 November 2026  
**Manuscript:** *Eulerian Fourier Profiles, Spectral Determinants, and Conformal Normalisations at the Special Point i/√2* — v14.10, sole Theorem 11.1 in §11.  
**Repository:** `ralfanop/Certifications_Eulerian_polar-curve_computations`  
**Autonomous branch:** `manuscript14-section11-parry-cert-20261103`  
**PR:** [#30](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/30) — **DRAFT, no merge**  
**Pinned Lean:** `v4.35.0-rc3`; **Mathlib:** `0272bbe1c093d038d7257ab15306abd58245f9ff`.

This register supersedes v6 **for status only**. Historical records and manuscripts 11–13, V007, V097 are untouched.

## Verified kernel checkpoints (never count a pending CI)

| Component | Last verified successful run | Additional audited Lean declarations |
|---|---|---:|
| Prior special-point theory (§§1–10 as applicable) | [#41723312459](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723312459) | 25 |
| Section 11: rational signs, floor dynamics, root existence/uniqueness, 12-decimal **analytic** bracket, strict defect, boundary jump, and unconditional integrated dynamical statement | [#41806320179](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41806320179) | 28 |
| Rational-digit affine orbits: monic polynomial, recurrence, repeated remainder ⇒ algebraic parameter, periodic digits ⇒ algebraic parameter | [#41808330602](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41808330602) | 7 |
| **Actual greedy integer floors**: remainder bounded by 1, affine digit recurrence, eventually periodic actual digits ⇒ algebraic β, transcendental β ⇒ digits aperiodic | [#41808771417](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41808771417) | 4 |
| Algebraic transfer: √2 algebraic, `exp(1/√2)` transcendental ⇒ `x_E` transcendental ⇒ actual greedy digits non-eventually-periodic | [#41809032863](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809032863) | 3 |
| Exact real sinh and rational Taylor series for `x_E` | [#41809760282](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809760282) | 2 |
| Algebraicity/nonzero of `1/√2` and final theorem reduced to an explicit Hermite–Lindemann hypothesis | [#41809760282](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809760282) | 2 |
| **Total Lean statements verified across successful checkpoints** | | **71** |

Each new theorem above has an explicit `#print axioms` audit. The permitted kernel axioms are `propext`, `Classical.choice`, `Quot.sound` (or subsets). No `sorryAx` or `Lean.ofReduceBool` was accepted by the successful runs.

**Do not interpret 71 as 71 independently novel paper theorems.** These are kernel-checked helper and main declarations supporting the *one* research theorem in §11.

## Arb / exact rational checks

The prior special-point workflow verified 37 checks. The current §11 Arb workflow independently verified 26 checks — the original 16 plus ten checks corresponding to the printed seven-term `s₆` Taylor enclosure in manuscript 14.10 — on [#41809439359](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809439359) (Arb job SUCCESS; the *Lean* job of that same run failed on a redundant `rfl` in an independent source file and cannot be counted as successful Lean). Thus **63 distinct Arb/exact checks are verified**. Finite ratio sampling alone is not a universal tail theorem; separate analytic bounds supply the rigorous enclosure.

## Additional certified modules — the latest clean checkpoint

[CI #41809760282](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41809760282) finished with **SUCCESS** in both Lean 4 and Arb, and the axiom audit is clean.

- `EulerianSinhSeries.lean` certifies the actual real hyperbolic sine Taylor identity and the exact series `x_E = Σ_{n≥0} 1/(2^n(2n+1)!)`, with two audited declarations.
- `EulerianTranscendenceReduction.lean` adds the algebraicity and nonvanishing of `1/√2`, and a theorem formally assembling the Eulerian transcendence and non-periodicity consequences **under a precisely stated Hermite–Lindemann hypothesis**, with two audited declarations.

The explicit hypothesis is **not** counted as a proven, unconditional classical theorem. The formal implication is kernel-checked; the premise remains open in this pinned library.

## Theorem 11.1 — exact verification boundary

**Already kernel-certified unconditionally:** the analytic definition of `x_E=√2 sinh(1/√2)` and its tight rational enclosure; the actual unique trinomial thresholds `β₃₂<x_E<β₃₁`; the literal greedy floor digits `1 0³⁰ 1` for `x_E` and terminating `1 0²⁹ 1` for `β₃₁`; the strict orbit-defect bounds; and the left-hand discontinuity at `β₃₁`.

**Already kernel-certified as general logical implications:** for any `β>1`, eventual periodicity of *actual floor-generated greedy digits* forces `β` to be algebraic; if `exp(1/√2)` is transcendental, so is `x_E`, hence its greedy digits are non-eventually-periodic.

**Outstanding:** a kernel proof of the classical Hermite–Lindemann special case
`¬IsAlgebraic ℚ (Real.exp (1 / Real.sqrt 2))`.
The pinned Mathlib snapshot has only `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`; Mathlib [PR #28013](https://github.com/leanprover-community/mathlib4/pull/28013), offering Lindemann–Weierstrass, remained open on 4 November 2026. There is no license to introduce the special case as an axiom or treat a conditional theorem as a completed *unconditional* certificate.

**No merge to PR #16, V007, V097 or `main`; manuscripts 11–13 unchanged.**
