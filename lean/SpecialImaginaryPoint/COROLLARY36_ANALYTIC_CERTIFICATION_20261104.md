# Manuscript 14.1 — Corollary 3.6: complete formal and analytic certificate

**Audit date:** 4 November 2026.  
**Manuscript package inspected:** `Manuscript_14_v14.1_Cor3.6_Lean4_Arb_CERTIFIED(3).zip`.  
**Isolated GitHub branch:** `manuscript14-cor36-lean-arb-20261104`.  
**Final successful joint workflow:** [#41824974185](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824974185), commit `0a645379268bf09189e4bec358286515019bb13f`.  
**Pinned toolchain:** Lean 4 v4.35.0-rc3 with the repository's pinned Mathlib; python-flint 0.9.0 at 256-bit Arb.

## 1. Corrected printed statement

`T : ℂ[[t]] → ℂ[[z²]]` acts by substitution `Tf(z)=f(-z²/16)` on **all formal inputs**; `D = z² ∂² + 2z ∂ + z²/4` acts on even series. The paper identities are:

`D T = 4 T L_F` and `D T B² = 4 T θ B² L_A`.

Unlike the older wording, the input `A(t)` need not be entire; it is a formal series. The Borel output `F=B²A` is entire. This is the only mathematical amendment relative to manuscript 14.10; Section 11 and the remaining mathematics were unchanged.

## 2. Kernel-verified six formal results

File: `lean/SpecialImaginaryPoint/Corollary36.lean`. Original [#41821155765](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41821155765) **SUCCESS**, reconfirmed by [#41824974185](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824974185).

- `evenEulerianDifferential_pullback`
- `evenEulerianDifferential_pullback_doubleBorel`
- `evenEulerianDPS_pullback`
- `evenEulerianDPS_pullback_doubleBorel`
- `operatorF_eulerianEntireCoeff_zero`
- `evenEulerianD_eulerianCoeff_zero`

These establish **universal coefficientwise / PowerSeries identities** over the prescribed formal series; no analytical convergence claim is inferred merely from formal coefficient equalities.

## 3. Six additional analytic results — NEW SUCCESS

File: `lean/SpecialImaginaryPoint/Corollary36Analytic.lean`. The latest [CI #41824974185](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824974185) compiled the module and verified:

- `eulerianEvenAnalytic_mul_eq_sin` — `(z/2)*F(-z²/16) = sin(z/2)` for every complex `z`.
- `eulerianEvenAnalytic_eq_sinc` — the actual entire Borel pullback is the continuous regularization `sin(z/2)/(z/2)`, including value 1 at zero.
- `eulerianEvenAnalytic_analyticAt` — genuine complex analyticity at every `z`.
- `eulerianEvenAnalytic_deriv_relation` — derivative identity `r_E + z r'_E = cos(z/2)`.
- `eulerianEvenAnalytic_second_deriv_relation` — second derivative relation `2 r'_E + z r''_E = -sin(z/2)/2`.
- `eulerianEvenAnalytic_differential_eq` — global complex ODE `z²r''_E+2zr'_E+(z²/4)r_E=0`, including at `z=0`.

The Lean CI explicitly prints `#print axioms` for all six results and the earlier six formal results. Only **`propext`, `Classical.choice`, `Quot.sound`** occur. **No `sorryAx`, no `Lean.ofReduceBool`, no custom mathematical axioms.** The previous failing runs were proof-elaboration/tactic issues, not theorems accepted with unsafe premises.

## 4. Arb / exact arithmetic certificate

File: `numerics/arb/manuscript14_cor36_arb.py`. In CI #41824974185 the numerical job completed **SUCCESS: 9/9**.

- First four tests: 64 exact rational coefficient instances of each formal family.
- Tail enclosure: a mathematically bounded positive Taylor remainder; 48-decimal scalar bounds.
- Certified `r_E(i/sqrt2) ≈ 1.020963929865019510478664635180421101946204326669871186445493706`.
- Differential residual at this point is rigorously smaller than `10^(-60)` in magnitude.

**Numerical checks at one special point do not imply a global operator identity.** The global claim is established by the independent Lean analytic proof, not by Arb.

## 5. Remaining scope beyond Corollary 3.6

This certificate completes the corrected **Corollary 3.6**, not every assertion elsewhere in Manuscript 14.1. In particular, no blanket claim is made about the spectral / Fredholm / modular geometry theorems of other sections. The unconditional Section 11 Eulerian–Parry theorem remains in the separate, audited branch `manuscript14-section11-parry-cert-20261103`, with its own attribution and no merge.

**No merges.** Do not modify V007, V097, manuscripts 11–13, `main`, or the original PDF/TeX to record this software audit.
