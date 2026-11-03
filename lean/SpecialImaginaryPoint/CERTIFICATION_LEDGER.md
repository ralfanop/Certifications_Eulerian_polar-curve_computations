# Certification ledger — version 4.0 (Manuscript 14.1)

**Issue date:** 3 November 2026.  
**Manuscript:** *The Special Point i/sqrt(2): Eulerian Fourier Profiles, Spectral Determinants, and Conformal Normalisations* — autonomous Manuscript **14**, version **14.1**.  
**Supersedes for this paper:** certification ledger v3 for pre-reduction Draft 0.10r6 (26 statements). The original v3 remains archived.  
**Source evidence SHA:** [`3c67a0f60093ccd50ec707ca351bd72147931daa`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/3c67a0f60093ccd50ec707ca351bd72147931daa).  
**Verified CI:** [#41682230079](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41682230079), **SUCCESS** in Lean and Arb, 3 November 2026 at 17:16 UTC.  
**Branch:** [`special-point-i-sqrt2-cert-20261103`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/tree/special-point-i-sqrt2-cert-20261103).  
**Status:** This documentation revision does **not** add new Lean proofs or certify additional complete manuscript statements.

## 1. Structural and notational compatibility with manuscripts 11–13

Manuscript 14 retains the notation of manuscript 13:
`r_E(z)=sin(z/2)/(z/2)`, `ν_λ`, `H_λ=L²([-1,1],ν_λ;ℂ)`,
`Φ_λ(w)=∫e^{iwu}dν_λ(u)`, the orthonormal `P_n^(λ)` basis, the
positive selfadjoint `D_λ`, coherent transform `C_(λ,α)`,
Gram `S_(λ,c)=C_(λ,α)^* C_(λ,α)` with `c=(4α)^(-1)`, and
`Dom` for domains. The present point and its parameter are
`z₀=i/√2=2ia`, `a=1/√8` and `z₁=i√2`.
**The Fourier phase convention matters:** the general transform uses
`e^(iwu)`, so `r_E(z)=Φ_(1/2)(z/2)` and **not** `Φ_(1/2)(z)`.
Here `D_(1/2)=-L_(1/2)` on the polynomial core. The Gram operator is
`S_(1/2,a)` on `H_(1/2)`; the separate auxiliary Dirichlet
Laplacian on `L²(0,1)` is `A=-d²/dt²`, and the reciprocal-central-binomial
generating function is the unrelated scalar `A(t)`.

**Non-duplication policy:** General ultraspherical measure,
normalisation, beta moments, Fourier–Bessel transform, Gegenbauer
spectrum and Fock transform/adjoint/Schatten results are cited from
manuscript 13, not independently asserted or re-proved here.
The classical uniform-law cumulant `Λ(s)=log(sinh(s/2)/(s/2))`
is cited from manuscript 12, Section 5. Its Langevin/variance
specialisations are stated only to support the new determinant comparison.
Previously proved Hall/Fock normalization is not restated as a new
section or result. The graph-domain proof of the new perturbed
Legendre–Gram commutation is retained because it is **not** proved
as such in manuscript 13.

## 2. Executive certification status

| Item | Status |
| --- | --- |
| Main statements currently printed in 14.1 | **20 = 6 Theorems + 11 Propositions + 3 Corollaries** |
| Fully Lean-certified with *every printed conclusion* | **0 / 20** |
| With partial certified subresults specific to the special point | **4 / 20** (Corollary 2.3, Proposition 3.1, Theorems 3.3 and 3.5) |
| Dedicated Lean modules compiled | **3** |
| Kernel-checked declarations, with explicit `#print axioms` | **15** |
| Arb / exact-rational checks in latest successful job | **37 PASS** |
| Printed scalar values verified to 50 significant digits | **10** (5 at each point) |
| Rational coefficients of even-zeta expansion checked exactly | **5** |
| Other numbered environments | 12 Remarks and 3 Questions (open questions are not asserted answers) |
| Overall progress as a percentage | **Not assigned**: proof-count percentages overstate completeness |

The **formal** identity `L_F ∘ B² = θ ∘ B² ∘ L_A` is
kernel-certified over Mathlib `PowerSeries ℂ`, including identification
of its operators with formal derivatives. That alone does not prove the
analytic continuation and entire-function equations printed in Theorem 3.5.

## 3. Exhaustive 20-row statement matrix

**PARTIAL** = some independently identified subclaims checked on the
new branch; **PENDING** = complete paper statement not yet certified.
Inherited results from 11–13 are not counted as proofs of new statements
without exact type, parameter and domain matching.

| Manuscript 14.1 result | Status | Remaining formal proof requirement |
| --- | --- | --- |
| Proposition 2.1 — Exact special-value chain | PENDING | Complex sin/sinh, modified spherical Bessel and `{}_0F_1` equality with justified infinite series |
| Corollary 2.3 — Explicit rational bounds | **PARTIAL** | Universal denominators and positivity checked; strict rational analytic remainder for **all N≥0** still required |
| Proposition 3.1 — Binomial input and beta integral | **PARTIAL** | Exact input coefficients and recurrence checked; beta integral, generating function and hypergeometric identity outstanding |
| Theorem 3.3 — Exact Borel–Eulerian specialisation | **PARTIAL** | Exact coefficient equality checked; analytic convergence/entire equality and special value not yet certified |
| Theorem 3.5 — Differential-operator identity under double Borel | **PARTIAL — central formal identity certified** | Formal identity on `PowerSeries ℂ` is proved; analytic ODE, input/output analytic identification and convergence remain |
| Corollary 3.6 — Eulerian second-order generator | PENDING | Quadratic pullback `t=-z²/16`, differential equation, analytic function domain |
| Proposition 3.7 — Modified-Bessel beta average | PENDING | Justify `I₀` integration and exchange with series |
| Proposition 4.1 — Axisymmetric Gegenbauer–Laplacian correspondence | PENDING | Angular-coordinate Laplace–Beltrami formula, exact `D_(1/2)=-L_(1/2)` operator sign and core |
| Theorem 4.2 — Cylindrical–spherical transmutation | PENDING | Full second-order intertwiner on even entire functions, extension at origin |
| Proposition 4.4 — Regular modified-Helmholtz profile | PENDING | Complete uniqueness, regularity and PDE |
| Proposition 5.1 — Special partition function and magnetisation | PENDING | Specialization of earlier cumulant law to normalized spherical integral, with exact probability assertions |
| Theorem 6.2 — Complete domain-level commutation | PENDING | Trace class inherited; prove special perturbed operator’s domain invariance and closed-graph commutation |
| Theorem 7.2 — Statistical–spectral determinant | PENDING | Dirichlet spectrum, trace-class Fredholm product and zeta determinant ratio |
| Theorem 7.3 — Langevin resolvent trace | PENDING | Trace = logarithmic derivative and second trace identity on actual operators |
| Corollary 7.4 — Hilbert–Schmidt trace | PENDING | Exact Hilbert–Schmidt norm of actual Dirichlet resolvent, not only Arb scalar |
| Proposition 7.5 — Convergent even-zeta expansion | PENDING | Analytic log/product expansion and convergence; five coefficients tested exactly |
| Proposition 8.1 — Quadratic L-value normalisation | PENDING | Character `χ₋₈` and class-number formula, all bridges to Borel/Fredholm |
| Proposition 8.2 — Class-number-one singular modulus | PENDING | Exact `j(i/√2)=8000`, class polynomial `H₋₈(X)=X-8000` |
| Proposition 8.3 — Modular equivalence without Eulerian equality | PENDING | Modular inversion, strict Eulerian inequality and complete separate trace/variance identities |
| Proposition 9.1 — Scalar factor in chiral generators | PENDING | Historical gamma-matrix basis and exact projector algebra |

## 4. Kernel-checked Lean declarations (15)

**Module `lean/SpecialImaginaryPoint/DenominatorRecurrence.lean` (4):**
`denominator_zero`,
`denominator_succ`,
`denominator_pos`,
`denominator_first_five`.

**Module `lean/SpecialImaginaryPoint/FormalBorel.lean` (5):**
`doubleBorel_intertwines`,
`doubleBorel_binomialInput_coefficients`,
`binomialInputCoefficient_recurrence`,
`operatorA_binomialInput_coefficient`,
`operatorF_eulerianBorel_coefficient`.

**Module `lean/SpecialImaginaryPoint/FormalBorelComplex.lean` (6):**
`doubleBorel_intertwines_complex`,
`doubleBorel_intertwines_powerSeries`,
`thetaPS_eq_X_derivative`,
`operatorAPS_eq_standard`,
`operatorFPS_eq_standard`,
`doubleBorel_intertwines_standard`.

All have `#print axioms` entries in the **SUCCESS** log.
Only `propext`, `Classical.choice` and `Quot.sound`
appear, sometimes as a subset. No `sorryAx` or
`Lean.ofReduceBool`. Pinned Lean:
`leanprover/lean4:v4.35.0-rc3`;
Mathlib: `0272bbe1c093d038d7257ab15306abd58245f9ff`.

## 5. Arb certification and boundaries

The pinned `python-flint==0.9.0` script at
[`numerics/arb/special_point_i_sqrt2_arb.py`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/3c67a0f60093ccd50ec707ca351bd72147931daa/numerics/arb/special_point_i_sqrt2_arb.py)
uses **256-bit** Arb interval arithmetic and exact rational fractions.
The [job](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41682230079) logged **37 PASS** checks. It checks
**five values at each point**, exact rounding to 50 significant digits:
Eulerian scalar, Langevin mean, orientation variance, Dirichlet resolvent
trace expression and its squared Hilbert–Schmidt expression.

It also checks five *supplied* classical even-zeta coefficients via
exact arithmetic, denominator recurrence at sample indices (the
universal identity is separately Lean-proved), one rational
truncation enclosure and numerical proximity of
`j(i/√2)` and `j(i√2)` to 8000.
No Arb enclosure proves the *exact* CM identity, and no scalar
numerical match proves the resolvent is trace-class or identifies its
operator trace.

## 6. Next obligations and publication controls

1. Complete Sections 2–3 analytically, using manuscript 13 results rather than duplicating ultraspherical proofs.
2. Certify the new axisymmetric operator identification in Section 4, then the distinct radial transmutation and Helmholtz statement.
3. Certify the *new* perturbed Legendre–Gram closed-domain commutation; do not re-prove the general Fock/Hilbert–Schmidt theorems of manuscript 13.
4. Formalize the auxiliary Dirichlet determinant, differentiability of trace identities and zeta-series convergence.
5. Verify the companion-point comparisons and the exact discriminant −8/CM identities, then chiral-generator normalization.
6. Audit every mathematical assertion in the 12 Remarks, cross-references, exact parameter conventions and the 20 main statements.

**No merges authorized:** Manuscript 14’s independent branch must not
be merged into V097, main or the open PR #16. Previous
manuscripts 11–13 remain unchanged. The v3 register for Draft
0.10r6 remains available for historical comparison but is not the
current statement matrix.

**Ledger version change:** v3 → **v4**; content adjusted to autonomous
Manuscript 14.1 and to its 20 printed statements after removal of
duplicate statements and proofs. **No additional Lean result is claimed.**
