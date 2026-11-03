# Certification ledger — version 2.0

**Manuscript:** *The Special Point i/sqrt(2): Eulerian Fourier Profiles, Spectral Determinants, and Conformal Normalisations*, independent draft **0.10r5** (3 November 2026).
**Ledger issued:** 3 November 2026.
**Proof-evidence commit:** [`5b9f99d6d53196bb8236bfececb66e99d21ef1f0`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/5b9f99d6d53196bb8236bfececb66e99d21ef1f0).
**Latest complete CI:** [GitHub Actions #41655638996](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41655638996): **SUCCESS for Lean and Arb**, completed 2026-11-03 14:41 UTC.
**Project branch:** [`special-point-i-sqrt2-cert-20261103`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/tree/special-point-i-sqrt2-cert-20261103).
**Scope:** This register applies *only* to the printed 0.10r5 manuscript. The proofs in manuscripts 11, 12 and 13 or V007/PR #16 do not automatically certify statements of this article.

## 1. Executive certification status

| Measurement | Verified status |
| --- | --- |
| Main mathematical statements in the manuscript | 22 = 6 Theorems + 12 Propositions + 4 Corollaries |
| Main statements certified in **every printed conclusion** | **0 / 22** under strict statement-by-statement matching |
| Main statements with **some** specific Lean certification | **4 / 22**: Corollary 2.3; Proposition 3.1; Theorems 3.3 and 3.5 |
| Main statements without dedicated Lean verification of their full conclusions | **18 / 22** (some have Arb evidence or potentially reusable theorems from prior papers) |
| Lean declarations printed in the latest clean axiom audit | **15** in **3** dedicated modules |
| Arb/exact-rational checks marked PASS by the latest numeric log | **24**; script exits successfully |
| Printed numerical values proved correctly rounded to 50 significant digits | **5 / 5** values explicitly checked in the script |
| Printed even-zeta expansion coefficients checked exactly | **5** rational coefficients |
| Precise overall completion percentage | **Not assigned**: a proof-count percentage would misrepresent the analytical/operator-theoretic workload |

**Interpretation:** The *central formal-power-series operator identity* in Theorem 3.5 is proved over Mathlib's `PowerSeries ℂ`. Its other printed conclusions about specific functions and analytic ODEs are not fully formalized. A numerical enclosure, even a rigorous Arb enclosure, is never counted as a proof of an operator identity.

## 2. Main-statement correspondence matrix (all 22)

Status codes: **PARTIAL** = a theorem of the new article has a dedicated kernel-checked subclaim; **PENDING** = no complete dedicated Lean proof of the printed statement has been confirmed. Numerical certification is recorded separately.

| Printed statement | Status | Kernel-checked coverage / remaining proof obligation |
| --- | --- | --- |
| Proposition 2.1 — Exact special-value chain | PENDING | Prove the complete sin/sinh, spherical/modified Bessel and `{}_0F_1` equality at `i/sqrt(2)`; justify the infinite Taylor sum |
| Corollary 2.3 — Explicit rational bounds | **PARTIAL** | Recurrence, positivity and five denominators checked in Lean; require the **strict bound for every N ≥ 0** and formal identification with the analytic special value |
| Proposition 3.1 — The binomial input and its beta integral | **PARTIAL** | Rational factorial coefficient and recurrence checked; require central-binomial generating function, `{}_2F_1` identity, beta moments/integral and analytic equality |
| Theorem 3.3 — Exact Borel–Eulerian specialisation | **PARTIAL** | Exact `4^n/(2n+1)!` coefficients checked; require convergence/entire equality, hypergeometric and sinh identities, and substitution `t=-z²/16` |
| Theorem 3.5 — Differential-operator identity under double Borel | **PARTIAL; central formal identity CERTIFIED** | `L_F B² = θ B² L_A` over all `PowerSeries ℂ` with standard-form operators; exact rational coefficient equations `L_A A=1/2`, `L_F F=0` checked. Still prove analytic ODEs and identify the particular formal series with the analytic functions |
| Corollary 3.6 — Eulerian second-order differential generator | PENDING | Formal/analytic pullback, second-order differential operator and equation for `r_E` |
| Proposition 3.7 — Modified-Bessel beta average | PENDING | Rigorous `I_0` expansion and beta integration, interchanges and integral identity |
| Proposition 4.1 — Two spherical realisations | PENDING | Sphere surface-measure marginal, both axis integrations and `I_0` representation at fixed parameter |
| Theorem 4.3 — Cylindrical–spherical transmutation | PENDING | Second-order identity on even entire functions, domain and origin behavior, `J_0` and `I_0` specialisations |
| Proposition 4.4 — Regular modified-Helmholtz profile | PENDING | `C²` radial regularity, PDE on `ℝ³`, boundary/initial data, uniqueness |
| Proposition 5.1 — Special partition function and magnetisation | PENDING | Exact sphere integral, Langevin derivative and variance identities; Arb has only scalar evaluations |
| Theorem 6.2 — Complete domain-level commutation | PENDING | Positivity, selfadjointness, trace class, smoothness, domain invariance, *closed-domain* commutation, boundary and trace identities |
| Corollary 6.3 — Matching Fock parameter | PENDING | Identify Gram kernel and `C* C` with matching measure and normalization; trace/HS interpretation |
| Proposition 6.4 — Second-order Gegenbauer–Fock transport | PENDING | Exact differential intertwiner on polynomial core, with stated conventions and Eulerian ODE |
| Theorem 7.2 — Common statistical–spectral determinant | PENDING | Dirichlet spectral realization, trace-class inverse, Fredholm product, **zeta-regularized determinant ratio** |
| Theorem 7.3 — Langevin resolvent trace | PENDING | Resolvent trace equals logarithmic derivative; twice-differentiated trace formula and operator-domain justifications |
| Corollary 7.4 — Hilbert–Schmidt trace at special point | PENDING | Actual resolvent HS norm and trace-square identities; Arb checks only the corresponding scalar expression |
| Proposition 7.5 — Convergent even-zeta expansion | PENDING | Analytic log/product expansion, absolute convergence and special zeta-value evaluations; five printed rational coefficients checked separately |
| Proposition 8.1 — Hall–Bargmann evaluation | PENDING | Gaussian integral, real evaluation coordinate `-ℏ/2` and exact prefactor, with the manuscript's convention |
| Proposition 9.1 — Quadratic L-value normalisation | PENDING | Exact `L(1,χ₋₈)=π/sqrt(8)`, `β(3)` evaluation and its formal links to Borel and Fredholm objects |
| Proposition 9.2 — Class-number-one singular modulus | PENDING | Exact CM value `j(i/sqrt(2))=8000` and `H₋₈(X)=X-8000`; an Arb ball near 8000 is *not* this proof |
| Proposition 10.1 — Scalar factor in chiral generators | PENDING | Chiral-projector algebra and precise historical gamma-matrix convention |

**Other manuscript content:** There are also **3 definitions**, **12 Remarks** and **3 open Questions**. The Questions need not be proved as affirmative results; independently checkable assertions in Remarks and mathematical statements outside theorem environments must still be audited before making a 100% certification claim.

## 3. Verified Lean 4 declarations — explicit audit index

The following **15** declarations occur in the successful CI's `#print axioms` output:

### `lean/SpecialImaginaryPoint/DenominatorRecurrence.lean` (4)

- `EulerianSpecialPoint.denominator_zero`
- `EulerianSpecialPoint.denominator_succ`
- `EulerianSpecialPoint.denominator_pos`
- `EulerianSpecialPoint.denominator_first_five`

### `lean/SpecialImaginaryPoint/FormalBorel.lean` (5)

- `EulerianSpecialPoint.doubleBorel_intertwines` — rational coefficient sequences
- `EulerianSpecialPoint.doubleBorel_binomialInput_coefficients` — exact binomial/Borel coefficients
- `EulerianSpecialPoint.binomialInputCoefficient_recurrence` — exact input recurrence
- `EulerianSpecialPoint.operatorA_binomialInput_coefficient` — `L_A A=1/2` coefficientwise over `ℚ`
- `EulerianSpecialPoint.operatorF_eulerianBorel_coefficient` — `L_F F=0` coefficientwise over `ℚ`

### `lean/SpecialImaginaryPoint/FormalBorelComplex.lean` (6)

- `EulerianSpecialPoint.doubleBorel_intertwines_complex` — arbitrary complex sequences
- `EulerianSpecialPoint.doubleBorel_intertwines_powerSeries` — all `PowerSeries ℂ`
- `EulerianSpecialPoint.thetaPS_eq_X_derivative` — `θ=X·d/dX`
- `EulerianSpecialPoint.operatorAPS_eq_standard` — identify `L_A` with its printed formal expression
- `EulerianSpecialPoint.operatorFPS_eq_standard` — identify `L_F` with its printed formal expression
- `EulerianSpecialPoint.doubleBorel_intertwines_standard` — printed full formal differential identity

**Formal method:** Lean `leanprover/lean4:v4.35.0-rc3`, Mathlib revision `0272bbe1c093d038d7257ab15306abd58245f9ff`, pinned in `lean/lean-toolchain` and `lean/lakefile.toml`. These modules compile through `lake env lean` within the dedicated workflow. Every printed axiom set contains only a subset of `propext`, `Classical.choice`, `Quot.sound`. The successful audit found no `sorryAx` or `Lean.ofReduceBool`.

**Proof log:** [Run #41655638996](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41655638996), `lean` job, checked against the source commit given above.

## 4. Arb and exact-rational verification ledger

**Script:** [`numerics/arb/special_point_i_sqrt2_arb.py`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/5b9f99d6d53196bb8236bfececb66e99d21ef1f0/numerics/arb/special_point_i_sqrt2_arb.py).

**Execution:** Python 3.13, `python-flint==0.9.0`, Arb context precision **256 bits**, 24 PASS results in [run #41655638996](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41655638996) (`arb` job).

1. **Five 50-significant-digit values:** special Fourier/Eulerian scalar; Langevin mean; orientation variance; Dirichlet resolvent-trace *expression*; squared Hilbert–Schmidt *expression*. For each, the printed decimal is strictly enclosed between the exact rational half-ULP rounding bounds.
2. **Rational data:** first five denominators, recurrence checked computationally at `n=0,...,39` (universal recurrence separately certified in Lean), one positive rational tail enclosure at **N=11**, and all **five** rational coefficients printed in the even-zeta expansion. The coefficient check uses the five *supplied* classical `ζ(2m)/π^(2m)` ratios; it does not independently prove those zeta evaluations.
3. **Additional Arb values:** `π/sqrt(8)` scalar, numerical estimates of the Langevin/variance/resolvent/HS expressions.
4. **Complex multiplication:** `j(i/sqrt(2))` overlaps 8000 and lies within `10^-40` of it, with a displayed Arb ball of radius below approximately `2.29×10^-71`. This is **not** a Lean proof of an exact singular-modulus identity.

**Important separation:** Numerical evidence for a scalar expression does not establish that it equals the trace or norm of the specific operator printed in the manuscript. Those analytical identification theorems are pending.

## 5. Prioritized proof-obligation plan

| Phase | Deliverable | Completion test |
| --- | --- | --- |
| A — close Sections 2–3 | Formal special-value chain, general `N` tail bound; analytic Borel transform, entire function, `{}_0F_1` and sinh identification; differential ODEs | Lean declarations cover *all* conclusions of Propositions 2.1, 3.1 and Theorems 3.3/3.5 plus Corollaries 2.3/3.6 |
| B — Sections 4–5 | Spherical marginal, `I_0`/`J_0`, second-order radial transmutation, Helmholtz uniqueness, Langevin derivatives | Exact measure, function-space, domain and differentiability assumptions in Lean |
| C — Section 6 | Positive trace-class Gram, parameter matching, closed-domain commutation and Fock transport | Domain invariance + graph-core/closure argument with an exact matching operator |
| D — Section 7 | Dirichlet realization, trace-class resolvent, Fredholm and zeta determinant, zeta-series convergence | Full operator identities and zeta-regularized ratio as printed |
| E — Sections 8–10 | Hall evaluation, exact Dirichlet character L-value, CM singular modulus, chiral scalar identity | Exact statements checked in Lean, not merely numerical agreement |
| F — final manuscript audit | Independently check mathematical assertions in Remarks, proof hypotheses, numeric literals and final LaTeX-to-Lean cross-reference | 22/22 complete matching + reproducible clean CI and axiom audits |

## 6. Reproducibility and safety constraints

- Do not merge this branch with `main`, V097, or PR #16 without explicit author approval.
- Do not modify the source packages 11, 12 or 13 merely to support this article.
- A separate `SUCCESS` label attaches to a **specific commit and job**, not to every statement that mentions the same operator or scalar.
- For each future theorem, record its printed manuscript label, actual Lean declaration, exact types/domains/parameters, source file and SHA, complete `#print axioms` output, workflow-run URL and whether it proves **all** or only **part** of the printed statement.
- A proof of an equality of formal series is not automatically a proof of an equality of entire functions, and a Hilbert-space identity on a polynomial core is not automatically an equality on a closed domain.
- All new versions of the register must identify the **manuscript revision** separately from the **repository branch/commit**, to avoid a false implication that a documentation-only commit produces additional mathematical certifications.

---

**Version change (v1 → v2):** A 22-row statement matrix, reproducibility snapshot, complete 15-declaration axiom index, exact-vs-numerical distinctions, explicit five-value rounding scope, zeta coefficient evidence, and phased criteria for 100% completion were added. **No additional mathematical proof is claimed by this documentation revision.**
