# Manuscript 14.1 — statement-level formalization roadmap

**Audited:** 4 November 2026; source package `Manuscript_14_v14.1_Cor3.6_Lean4_Arb_CERTIFIED(3).zip`.  
**Relationship to v14.10:** source comparison found a single substantive mathematical amendment, **Corollary 3.6**, replacing the unjustified "even entire inputs" restriction by the correct formal source `ℂ[[t]]` and target `ℂ[[z²]]`. All other mathematical statements, including Section 11, were retained.

## Audited results and evidence

- **Corollary 3.6, Section 3: COMPLETED IN LEAN AND ARB.**
  - [CI #41824974185](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824974185) on `0a645379268bf09189e4bec358286515019bb13f` is SUCCESS in both jobs.
  - Six formal coefficient/PowerSeries results in `Corollary36.lean` and **six additional genuinely analytic results** in `Corollary36Analytic.lean`.
  - In particular the real analytic Borel pullback equals the complex regularized sinc `r_E(z)` *globally* and obeys `z² r''_E + 2 z r'_E + z²/4 r_E=0` for every complex `z`, including zero.
  - All printed audit axioms are only `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, `Lean.ofReduceBool`, or custom axioms. The numerical script has 9/9 exact/Arb checks at 256-bit precision; pointwise Arb alone would not certify the analytic ODE.

- **Theorem 11.1, Section 11: COMPLETED IN ITS OWN ISOLATED BRANCH.**
  - [CI #41812736721](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41812736721) jointly verified the unconditional Eulerian–Parry result with imported and kernel-compiled Apache-2.0 Lindemann proof sources, and 26/26 Arb checks.
  - [Section 11 ledger v8](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/manuscript14-section11-parry-cert-20261103/lean/SpecialImaginaryPoint/CERTIFICATION_LEDGER_v8.md).
  - Theorem 11.1 is unchanged between v14.10 and v14.1; no need to repeat or claim as new any classic Parry proofs in the manuscript.

## Remaining printed results: certification status needs theorem-by-theorem matching

The manuscript has the following *additional* printed results. They are listed as **NOT YET VERIFIED AS COMPLETE KERNEL THEOREMS FOR THIS EXACT PAPER STATEMENT** in this roadmap, regardless of whether individual identities are classical or there are related Lean theorems in manuscripts 11–13/V007. Do not confuse related library lemmas with matching operator domains/normalisations.

| Section | Printed result | Formalization obligation |
| --- | --- | --- |
| 2 | Proposition — Exact special-value chain | Match every identity with the actual sinc and numerical normalisation |
| 2 | Corollary — Explicit rational bounds | Verify all interval bounds and rational tail conditions |
| 3 | Proposition — The binomial input and its beta integral | Formal beta integral evaluation; Borel-compatible coefficients |
| 3 | Theorem — Exact Borel–Eulerian specialisation | Connect formal double-Borel identity with actual convergent functions (some imported results already exist) |
| 3 | Theorem — A differential-operator identity under double Borel transform | Confirm domain and intertwining normalization beyond Corollary 3.6 |
| 3 | Proposition — Modified-Bessel beta average | Prove relevant beta-average integral exactly |
| 4 | Proposition — Axisymmetric Gegenbauer–Laplacian correspondence | Correct dimensional parameter and analytic domain |
| 4 | Theorem — A second-order cylindrical–spherical transmutation | Differential identities and radius-zero regularity |
| 4 | Proposition — Regular modified-Helmholtz profile | PDE statement and normalization |
| 5 | Proposition — Special partition function and magnetisation | Partition integral, derivatives, variance |
| 6 | Theorem — Complete domain-level commutation | **Priority**: common core, closures, domains, and strong operator identity, not just polynomial formalities |
| 7 | Theorem — A common statistical–spectral determinant | **Priority**: trace-class/Fredholm determinant operator realization and scalar evaluation |
| 7 | Theorem — Langevin as a resolvent trace | Legitimate differentiation/traces, convergence and spectral normalization |
| 7 | Corollary — A Hilbert–Schmidt trace at the special point | Verify the actual Hilbert-space operator and the scalar identity |
| 7 | Proposition — A convergent even-zeta expansion | Convergence and exact even-zeta coefficients, not just finite numerics |
| 8 | Proposition — Quadratic L-value normalization | Character/Dirichlet L-series at the specified discriminant |
| 8 | Proposition — Class-number-one singular modulus | CM theorem or exact modular-form identity, not approximate Arb overlap |
| 8 | Proposition — Modular equivalence without Eulerian equality | Modular inversion and distinct Eulerian scalar values |
| 9 | Proposition — Scalar factor in chiral generators | Exact normalization and matrix/operator conventions |

The introduction, §§10,12 and appendix contain additional narrative assertions to audit; this table only enumerates the named printed statements from the TeX source. A result is not called "uncertified" as a mathematical assertion merely because its exact Lean formalization has not yet been verified.

## Execution order

1. Preserve the already certified **Section 3 Corollary 3.6** and **Section 11 Theorem 11.1** as separate independent branch evidence. No merge.
2. For the next new research theorem, prioritize **§6 domain-level Gram commutation**, then **§7 determinant/trace realization**; these are genuine operator-theoretic obligations that cannot be discharged by Arb scalar checks.
3. Reuse the existing Gegenbauer/L²/Fock mathematical library where exact operator types and parameters match; otherwise prove bridges, not just a relabeled lemma.
4. Add Arb intervals only for explicit scalar constants and special-point values; **do not claim numerical certification of infinite-dimensional identities**.
5. Update the manuscript's appendix statement by statement only after successful kernel checks.

No changes to the author's original TeX/PDF, V007, V097, manuscripts 11–13 or `main`.
