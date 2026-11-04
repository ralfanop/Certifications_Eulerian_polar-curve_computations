# Manuscript 14.10 — Section 11 certification ledger v6

**Date:** 4 November 2026. **Scope:** sole printed Theorem 11.1 of manuscript 14.10, and prior special-point modules.

The historic `CERTIFICATION_LEDGER_v5.md` remains unmodified. The autonomous [PR #30](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/30) remains **DRAFT — DO NOT MERGE**.

## Verified successful checkpoints

| Workstream | Successful CI | Lean declarations explicitly axiom-audited | Arb exact/ball checks |
| --- | --- | ---: | ---: |
| Prior Sections 1–10 special-point modules | [#41723312459](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723312459) | 25 | 37 |
| Section 11 complete numerical + dynamical certification | [#41806320179](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41806320179) | 28 | 16 |
| **Verified combined baseline** | Both successful checkpoints | **53** | **53** |

The new generic repeated-affine-orbit module is in CI and **is not included in these certified counts** until independently successful. Only `propext`, `Classical.choice`, and `Quot.sound` (or subsets thereof) occur in the successful Lean kernel audit.

## Theorem 11.1 — detailed status

1. **Exact analytic special value and rational enclosure — CERTIFIED.** The real number `eulerianParryValue := sqrt(2) * sinh(1 / sqrt(2))` satisfies the rigorous rational enclosure `1085441641272/10^12 < x_E < 1085441641273/10^12`, proved using Mathlib exponential Taylor bounds and no Arb assumptions. See `EulerianAnalyticBracket.lean` and [#41805294957](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805294957).
2. **Adjacent trinomial roots — CERTIFIED.** Existence/uniqueness of `beta_31` and `beta_32`, then `beta_32 < x_E < beta_31`. See `parry32_exists_unique_root`, `parry_adjacent_roots_straddle`.
3. **Actual floor-based greedy map and exact digit blocks — CERTIFIED.** The floor map `greedyMap beta x := beta*x - floor(beta*x)`, including input-one convention, initial `1 0^30 1` digits for `x_E`, and the terminal `1 0^29 1` at `beta_31`. See `ParryThresholds.lean`.
4. **Defect and left jump — CERTIFIED.** `313240/10^9 < 1 - T_xE^31(1) < 313241/10^9`, `T_beta31^31(1)=0` and its left-hand limit 1. The unconditional integrated theorem `eulerian_parry_dynamical_part_unconditional` is kernel-checked by [#41806320179](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41806320179).
5. **Transcendence of `x_E` — NOT KERNEL-CERTIFIED.** Mathematical argument: nonzero algebraic `a=1/sqrt2`; Hermite–Lindemann implies `y=exp(a)` transcendental. If `s=sinh(a)` were algebraic, `y^2-2*s*y-1=0` would make `y` algebraic, contradiction. Multiplication by nonzero algebraic `sqrt2` preserves transcendence. A directly applicable Hermite–Lindemann theorem has not been located in the pinned Mathlib snapshot; do not introduce a theorem as an axiom.
6. **Non-eventual periodicity of greedy digits — NOT KERNEL-CERTIFIED.** Mathematical argument: periodic digit tail gives a finite rational generating function and a nonzero monic integer polynomial at beta; hence beta algebraic, contradicting §5. Formal missing steps include the telescoping expansion, a geometric digit tail, and nonzero polynomial. The generic repeated-state affine-orbit lemma is only an intermediate result, not the missing implication from periodic digits.

## Active proof module

`lean/SpecialImaginaryPoint/PeriodicOrbitAlgebraicity.lean` attempts four generic intermediary declarations: monic polynomial representation of finite rational-digit affine orbits, evaluation agreement, degree separation, and algebraicity of beta if two orbit states repeat. Its current CI is [#41807371625](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41807371625), not counted as successful before verification.

The mathematical proofs and further Lean obligations are recorded in [`research/Manuscript14_Section11_Transcendence_Periodicity_Proof_Obligations.md`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/manuscript14-section11-parry-cert-20261103/research/Manuscript14_Section11_Transcendence_Periodicity_Proof_Obligations.md).

**Do not merge PR #30; no modifications to V007, V097, other manuscripts, or their PDFs.**
