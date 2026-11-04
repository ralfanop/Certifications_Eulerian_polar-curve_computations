# Manuscript 14.1 — Section 4 Sonine certificate scope

**Date:** 4 November 2026  
**Source manuscript:** `Manuscript_14_v14.1_Cor3.6_CERTIFIED_Bibliography_Corrected.zip`, SHA-256 `9dd5c527d7312f3285a26d318061ad38430347378275f4ae7a8f02fd5a3a62d5`.  
**Repository branch:** `manuscript14-sonine-radial-20261104`, based on `manuscript14-cor36-lean-arb-20261104`.  
**Final successful joint workflow:** [CI #41824320150](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824320150) at commit `03f130979fa00d4d8546e37a8f8eab3b8fa0566c` — **Lean SUCCESS; Arb 12/12 PASS**, both jobs completed 4 November 2026. An earlier CI #41823916721 had one harmless Lean tactic sequencing error (`No goals to be solved`) and Arb SUCCESS; the revised source passed at the final CI.  
**Change isolation:** no merge, no TeX/PDF edits, no changes to V007, V097, manuscripts 11–13 or PR #30.

## Formal mathematical target

Theorem `thm:sonine` in §4 asserts that the even-entire-function integral map

`(Mf)(t)=(1/2) ∫_{-1}^1 f(t sqrt(1-u²)) du`

intertwines `H3 = d²/dt²+(2/t)d/dt` and `H2 = d²/dt²+(1/t)d/dt`.

The coefficient moments are

`c_n=(1/2) ∫_{-1}^1 (1-u²)^n du = 4^n (n!)²/(2n+1)!`

with `c_0=1` and `(2n+3)c_(n+1)=(2n+2)c_n`.

**What the new Lean module claims:** [SonineRadialFormal.lean](../lean/SpecialImaginaryPoint/SonineRadialFormal.lean) constructs the rational recurrence `c_n` and proves its positivity, the recurrence, and coefficientwise `H3 M = M H2` on every rational sequence; it also states and proves the same identity in Mathlib's `PowerSeries ℚ` (variable `u=t²`). **CERTIFIED:** the isolated Lean job has passed, and `#print axioms` for `moment_pos`, `moment_recurrence`, `radial_intertwining_coeff`, and `radial_intertwining_powerSeries` lists only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or `Lean.ofReduceBool` was reported. The rational moment is initially defined by recurrence. **NEW SUCCESS:** [CI #41838692304](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41838692304) kernel-checked `SonineIntegralMoment.lean`, proving the actual integral identity `(1/2)∫_{-1}¹(1-u²)^n du = (moment n : ℝ)` for **every** `n : ℕ` by FTC, including its base case and exact recurrence. The log of `integralMoment_zero`, `integralMoment_recurrence`, `integralMoment_eq_moment`, and `integral_monomial_sonine` lists only `propext`, `Classical.choice`, `Quot.sound`, with no forbidden axiom. The explicit gamma/factorial expression is not yet separately linked as a Lean theorem.

**What the Arb/exact script claims:** [manuscript14_sonine_radial_arb.py](../numerics/arb/manuscript14_sonine_radial_arb.py) has 12/12 independent checks PASS on the CI Arb job: exact moment recurrences through `n=100`, 81 exact integrated-binomial moments, four rational-polynomial profile tests for 129 coefficients, Bessel-to-spherical coefficients through `n=100`, and a rigorous 256-bit Arb special-value enclosure. This is *finite exhaustive checking for the listed ranges*, not a universal mathematical proof.

The rigorous Arb interval comparisons establish that the special imaginary sinc `r_E(i/sqrt(2))` and `sinh(1/sqrt(8))/(1/sqrt(8))` agree to absolute error below `10^-60` at the designated point. The mathematical equality remains the classical sine/hyperbolic identity, not a consequence of numerical proximity alone.

## Outstanding work to formalize full Theorem 4

1. **DISCHARGED**: the actual monomial moment integral equals the formal rational coefficient for all natural indices — [CI #41838692304](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41838692304).
2. **IN REVIEW**: [SonineEvenPolynomials.lean](../lean/SpecialImaginaryPoint/SonineEvenPolynomials.lean) defines the exact real averaging operator with `sqrt(1-u²)` and targets all even monomials and finite real-coefficient even polynomials; [CI #41839414136](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41839414136) must complete successfully before these theorems are counted.
3. **OPEN**: show uniform convergence of the even entire Taylor series and its differentiated series on every compact set; use this to justify differentiation and integration termwise, including `t=0`.
4. **OPEN**: lift `H3 M f = M H2 f` from even polynomials to all even entire functions, and establish `M J0=j0` and `M I0(a)=sinh(a)/a` as analytic identities.
5. **OPEN**: separately audit the regular modified-Helmholtz profile proposition, especially uniqueness.

## Integrity

The earlier 14.1 audit also identified outstanding results in §6 (actual Gram-domain commutation), §7 (Fredholm/zeta and resolvent traces), and §§2–3, 5, 8. Their status is unchanged. Existing Corollary 3.6 and Theorem 11.1 certificates are separate and not recomputed by this Sonine workflow.

The original toolchain pin Lean `v4.35.0-rc3` and Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff` are not changed.
