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

Additional [384-bit Arb/exact-rational CI #41840331071](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41840331071) and final [combined CI #41840598183](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41840598183) (**both Lean and Arb jobs SUCCESS**), executed with the pinned `python-flint==0.9.0`, reports **7/7 new PASS**: exact integrated moments through `n=85`, 540 exact rational polynomial profiles for the genuine average and radial differential expressions, exact zero-radius checks, 21-term strict rational Taylor enclosures, and complex Arb special-point cross-check. An earlier attempt at 256 bits was not sufficient to separate the extremely narrow 21-term *upper* tail enclosure; precision was increased to 384 bits, not the interval tolerance. This additional numeric job is distinct from the earlier 12/12 Sonine checks; neither finite numeric suite proves the universal analytic result.

Final CI #41840598183 is the last full-run evidence for the new complex-formal Lean and 384-bit Arb workstreams. The manuscript version and pinned dependencies were unchanged.\n\nThe rigorous Arb interval comparisons establish that the special imaginary sinc `r_E(i/sqrt(2))` and `sinh(1/sqrt(8))/(1/sqrt(8))` agree to absolute error below `10^-60` at the designated point. The mathematical equality remains the classical sine/hyperbolic identity, not a consequence of numerical proximity alone.

## Certified progress since §4's initial 12/12 Arb / Lean formal result

Kernel-certified extensions: genuine real moments for every natural index; exact real integral action on all even polynomials; complex formal coefficient and `PowerSeries ℂ` intertwining. The linked CI logs have been inspected for standard axiom dependencies and forbidden axioms. These are new research-software certificates, not new general Sonine theory.

## Certified factorial and Bessel transformations (4 November 2026)

The isolated [CI #41848633944](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41848633944) finished **SUCCESS** in both the Lean and Arb jobs.

- [SonineFactorialMoment.lean](../lean/SpecialImaginaryPoint/SonineFactorialMoment.lean): `integralMoment_eq_factorial` verifies in the Lean kernel for every `n : ℕ` the explicit printed formula
  `(1/2)∫_{-1}¹(1-u²)^n du = 4^n (n!)²/(2n+1)!`.
- [SonineBesselCoefficients.lean](../lean/SpecialImaginaryPoint/SonineBesselCoefficients.lean): `sonine_modifiedBessel_coefficients` and `sonine_ordinaryBessel_coefficients` certify the coefficientwise transform `c_n /(4^n(n!)²)=1/(2n+1)!` and its `(-1)^n` variant for all n. Their axiom audits show only `propext`, `Classical.choice`, `Quot.sound`.
- [manuscript14_sonine_bessel_tails_arb.py](../numerics/arb/manuscript14_sonine_bessel_tails_arb.py): **35/35 PASS**, python-flint 0.9.0 at 384-bit precision. This covers exact J₀/I₀-to-spherical coefficients through n=180, and strict spherical Taylor interval bounds for radii 1,2,4,8 and truncations 12,16,24,30.

These results are not a claim that global analytic identities `M(J₀)=j₀` or `M(I₀)=sinhc` are fully formalized: the pointwise interchange of an infinite Taylor sum with the integral is still being checked separately. The exact scalar identity for every monomial **is** already kernel-certified.

## Actual entire-series identity: kernel certified

**SUCCESS:** [CI #41850369477](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41850369477), with the pinned Lean/Mathlib stack and clean axiom audit, proves a global analytic statement that is strictly stronger than the previous finite polynomial identity:

For any complex sequence `a : ℕ → ℂ` such that `∑ ‖a_n z^(2n)‖ < ∞` for every `z : ℂ`, set `f(z)=∑' n, a_n z^(2n)`. Then

`(Mf)(z) = (1/2)∫_{-1}¹ f(z sqrt(1-u²)) du = ∑' n, a_n c_n z^(2n)`, where `c_n=4^n(n!)²/(2n+1)!`.

The kernel proof uses continuous complex integrands, Mathlib dominated convergence on the *real interval*, exact monomial moments and global pointwise equality of the `tsum` with the integral. **No differentiability or second-order radial identity for arbitrary entire f is claimed yet**. This result does not by itself identify any particular unqualified classical `BesselJ`/ `BesselI` function.

The next [SonineBesselGlobal.lean](../lean/SpecialImaginaryPoint/SonineBesselGlobal.lean) applies this to the series-defined cylindrical Bessel functions and Mathlib's classical `Complex.sin/sinh`; [SonineBesselSummability.lean](../lean/SpecialImaginaryPoint/SonineBesselSummability.lean) targets universal coefficient absolute convergence. This latter workstream is not counted without separate successful CI.

## Outstanding work to formalize full Theorem 4

1. **DISCHARGED**: the actual monomial moment integral equals the formal rational coefficient for all natural indices — [CI #41838692304](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41838692304).
2. **DISCHARGED**: [SonineEvenPolynomials.lean](../lean/SpecialImaginaryPoint/SonineEvenPolynomials.lean) defines the actual real averaging operator with `sqrt(1-u²)` and proves the exact action on all even monomials and finite even polynomials with real coefficients. [CI #41839414136](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41839414136) — **SUCCESS**; `sonineAverageReal_even_monomial` and `sonineAverageReal_evenPolynomial` audited with only standard axioms.
3. **DISCHARGED (FORMAL SERIES)**: [SonineRadialComplex.lean](../lean/SpecialImaginaryPoint/SonineRadialComplex.lean) extends `H3 M = M H2` coefficientwise to arbitrary `ℕ → ℂ` and to Mathlib `PowerSeries ℂ`. [CI #41839935793](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41839935793) — **SUCCESS**, with `momentComplex_recurrence`, `radial_intertwining_coeff_complex`, and `radial_intertwining_powerSeries_complex` each using only the three standard axioms.
4. **OPEN**: show uniform convergence of the even entire Taylor series and its differentiated series on every compact set; use this to justify differentiation and integration termwise, including `t=0`.
5. **DISCHARGED (INTEGRAL / ENTIRE SERIES)**: [CI #41850369477](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41850369477) is SUCCESS. [SonineEvenComplexPolynomials.lean](../lean/SpecialImaginaryPoint/SonineEvenComplexPolynomials.lean) proves the actual complex Bochner Sonine integral on every even complex polynomial; [SonineEntireInterchange.lean](../lean/SpecialImaginaryPoint/SonineEntireInterchange.lean) proves dominated-convergence exchange at every complex z with ∑‖aₙz^(2n)‖ finite; [SonineEntireAveraging.lean](../lean/SpecialImaginaryPoint/SonineEntireAveraging.lean) proves the actual global integral identity for every such entire coefficient sequence. All six audited declarations in the new modules list only `propext`, `Classical.choice`, `Quot.sound` and no forbidden axioms. **OPEN**: Lift `H3 M f = M H2 f` from even polynomials to all even entire functions, and establish `M J0=j0` and `M I0(a)=sinh(a)/a` as analytic identities.
6. **OPEN**: separately audit the regular modified-Helmholtz profile proposition, especially uniqueness.

## Integrity

The earlier 14.1 audit also identified outstanding results in §6 (actual Gram-domain commutation), §7 (Fredholm/zeta and resolvent traces), and §§2–3, 5, 8. Their status is unchanged. Existing Corollary 3.6 and Theorem 11.1 certificates are separate and not recomputed by this Sonine workflow.

The original toolchain pin Lean `v4.35.0-rc3` and Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff` are not changed.
