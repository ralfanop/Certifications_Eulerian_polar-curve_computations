# Special point i/sqrt(2) — certification ledger (Draft 0.10r5)

This branch is intentionally independent of manuscripts 11, 12 and 13, the
existing PR #16, and the approved V097. Do not merge without the author's
separate approval.

Source: `Eulerian_i_sqrt2_Draft10r5.tex`. Each proof must match the **entire
printed statement**, not merely a finite-dimensional surrogate or a scalar
instance.

Legend: **pending** = not yet shown to be kernel-certified on this branch;
**partial** = the file proves only explicitly listed subclaims; **Arb** =
rigorous *scalar enclosure* from python-flint, NOT a proof of analytic identity.

| Printed result | Formalization status | Next Lean obligation |
|---|---|---|
| Proposition 2.1 Exact special-value chain | pending; classical special-function identities | Complex sin at imaginary argument; spherical/modified Bessel and 0F1 equality |
| Corollary 2.3 Explicit rational bounds | **partial**: universal integer denominator recurrence and Arb enclosure for one finite truncation | Prove strict infinite-series remainder bound for all N and identify with the analytic value |
| Proposition 3.1 Binomial input and beta integral | **partial**: factorial coefficient recurrence and exact rational binomial input | Generating-function sum, hypergeometric identity, and beta integral |
| Theorem 3.3 Exact Borel–Eulerian specialisation | **partial**: exact factorial coefficient equality under double Borel | Entire convergence and evaluation as sinh/0F1 for all complex t and the substitution t=-z²/16 |
| Theorem 3.5 Differential-operator identity | **central identity certified** on PowerSeries ℂ, including standard θ=X·d/dX and L_A,L_F; **input equations certified coefficientwise** over ℚ | Differential equations for analytic A,F and their convergence, plus equivalence of coefficient-specific input with analytic functions |
| Corollary 3.6 Eulerian second-order generator | pending | Pull-back by t=-z²/16 and differential equation |
| Proposition 3.7 Modified-Bessel beta average | pending | Beta integral, I0 expansion, exchange |
| Proposition 4.1 Two spherical realisations | pending; V007 sphere-marginal background available | Concrete area measure and I0 spherical integrals |
| Theorem 4.3 Cylindrical–spherical transmutation | pending | Equality on explicit differentiable domain |
| Proposition 4.4 Regular modified-Helmholtz profile | pending | C² radial equation, origin, uniqueness |
| Proposition 5.1 Special partition function and magnetisation | pending; Arb scalar enclosures | Integral, first and second log derivatives |
| Theorem 6.2 Complete domain-level commutation | pending; PR #16 Sturm work is NOT this theorem | Integral commutant, selfadjoint realization, exact domain |
| Corollary 6.3 Matching Fock parameter | pending | Scalar normalization with positive inputs |
| Proposition 6.4 Second-order Gegenbauer–Fock transport | pending | Exact differential intertwiner and analytic domain |
| Theorem 7.2 Statistical–spectral determinant | pending | Dirichlet eigenvalues, trace-class inverse, Fredholm product |
| Theorem 7.3 Langevin resolvent trace | pending; Arb scalar enclosure | Trace sum equals coth formula |
| Corollary 7.4 Hilbert–Schmidt trace | pending | Positive operator, HS trace and exact series |
| Proposition 7.5 Even-zeta expansion | pending | Log product and absolutely convergent series |
| Proposition 8.1 Hall–Bargmann evaluation | pending | Concrete transform and Gaussian cancellations |
| Proposition 9.1 Quadratic L-value normalization | pending | Quadratic L special values, discriminant −8 |
| Proposition 9.2 Class-number-one singular modulus | pending | CM j(i/sqrt2)=8000, correct modular normalization |
| Proposition 10.1 Hepner chiral scalar factor | pending | Gamma-matrix conventions and exact algebraic identity |

## Checked certifications for Draft 0.10r5 (2026-11-03)

### Lean 4, pinned `v4.35.0-rc3` and Mathlib `0272bbe1`

1. `lean/SpecialImaginaryPoint/DenominatorRecurrence.lean`:
   `denominator_zero`, `denominator_succ`, `denominator_pos`,
   `denominator_first_five`.
2. `lean/SpecialImaginaryPoint/FormalBorel.lean`:
   `doubleBorel_intertwines` over ℚ, `doubleBorel_binomialInput_coefficients`,
   `binomialInputCoefficient_recurrence`,
   `operatorA_binomialInput_coefficient`, and
   `operatorF_eulerianBorel_coefficient`.
3. `lean/SpecialImaginaryPoint/FormalBorelComplex.lean`:
   `doubleBorel_intertwines_complex`,
   `doubleBorel_intertwines_powerSeries`,
   `thetaPS_eq_X_derivative`, `operatorAPS_eq_standard`,
   `operatorFPS_eq_standard`, and
   `doubleBorel_intertwines_standard`.
   These last four declarations identify the operators with their literal
   standard differential expressions on Mathlib's `PowerSeries ℂ` type.

CI for complete current proof modules and global axiom printout:
[41654902000](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41654902000)
at commit `974ad40dfeb77417c662021b7b691e0016ccc1d6`: **SUCCESS**.
All listed `#print axioms` declarations depend only on `propext`,
`Classical.choice`, `Quot.sound` (some use a subset).
Neither `sorryAx` nor `Lean.ofReduceBool` occurs in the proof audit.

**Precise interpretation:** The full core *formal* operator identity of
Theorem 3.5 is certified on ℂ[[t]], together with its rational input and
output coefficient equations. This does NOT yet prove convergence of the
analytic functions or the printed second-order analytic ODEs.

### Arb and exact rational arithmetic

The independent numerical script
`numerics/arb/special_point_i_sqrt2_arb.py` (python-flint 0.9.0,
256-bit Arb) certifies correct rounding of the five *printed* 50-significant-digit
values; exact finite rational remainders; and the scalar enclosure of Klein's
`j(i/sqrt(2))` within `1e-40` of `8000`. The latter is *not*
an exact CM equality proof. These checks were verified with SUCCESS
on the same GitHub workflow and previously on run
[41639135411](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41639135411).

### Still required for 100% certification

Complete the unverified portions of the 22 printed main statements, all
independent mathematical assertions in Remarks, analytic convergence, the
spherical transmutation and Helmholtz boundary problem, actual closed-domain
Legendre–Gram commutation, trace-class Fredholm/zeta determinant, the Hall
transform, and exact CM/Dirichlet-L-value statements. Existing results from
manuscripts 11–13 may be reused only after exact hypothesis matching.

## Non-transfer principle

A successful module of manuscript 13/V007 certifies only its actual Lean
statement, not a similar theorem of the present article. Existing proof
modules are evidence to reuse, not licenses to mark this ledger as completed.
Do not label any part "Lean certified" without matching SHA, successful
kernel compilation, `#print axioms` and audit of forbidden axioms.
