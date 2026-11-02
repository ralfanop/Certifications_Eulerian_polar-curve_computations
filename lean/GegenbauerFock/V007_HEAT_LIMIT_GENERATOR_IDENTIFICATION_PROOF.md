# V007 — Identification of the genuine Gegenbauer heat semigroup generator

**Status (2 November 2026):** The complete generator–canonical-Sturm graph equality is now Lean 4 kernel-certified at source commit `ae52253f87b3a93410c0d6799f78b7e647e0daa4` by CI [41438637991](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41438637991) (SUCCESS, 9,132 jobs, clean `#print axioms` audit). The mathematical proof below and the historical checklist remain for exposition; this Markdown file is not itself a kernel certificate. Certification attaches to the exact Lean declarations and source blob.

## 1. Framework and established bridge

Fix `lambda > 0`. Let `H = L²(nu_lambda; R)` be the actual weighted real Hilbert space, and denote by `(e_n)_(n≥0)` the genuine normalized Gegenbauer Hilbert basis constructed in
`UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis.lean`.

Put `omega_n = n(n+2 lambda)`. The canonical closure `A` of the actual polynomial Sturm–Liouville operator has been identified in
`UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure.lean` with the diagonal operator

`Dom(A) = {f in H : sum_n omega_n² |<f,e_n>|² < infinity}`,
`<Af,e_n> = -omega_n <f,e_n>`.

This exact *domain* equality is essential: merely checking eigenpolynomials or constructing a spectral extension is insufficient.

For each `s ≥ 0`, the strong Yosida limit `H_s` is a bounded contraction on the entire actual weighted `L²`, with

`H_s e_n = exp(-s omega_n) e_n`.

The named Lean modules for these prior ingredients are:
`UltrasphericalSturmLiouvilleRealYosidaAllL2StrongLimit.lean`,
`UltrasphericalSturmLiouvilleRealHeatLimitCLM.lean`, and
`UltrasphericalSturmLiouvilleRealHeatLimitEigenmodes.lean`.
The semigroup law and strong continuity have separate modules; consult their exact CI status.

## 2. Diagonal heat action for arbitrary f in L²

For a general `f = sum_n c_n e_n`, let
`f_N = sum_(n≤N) c_n e_n`. Since `f_N -> f` in `H` and `H_s` is bounded,

`H_s f = lim_N H_s f_N = sum_n exp(-s omega_n)c_n e_n`

in the **genuine L² norm**. This follows by continuity and the established exact action on each basis vector. The resulting coefficient identity is

`<H_s f,e_n> = exp(-s omega_n)<f,e_n>`.

No analytic kernel formula, abstract succession space, or additional self-adjointness assumption is needed for this step.

## 3. Exact identification of the generator domain

Define the right infinitesimal generator `G` by

`Dom(G) = { f in H : lim_(s↓0) (H_s f-f)/s exists in H }`,
`G f = lim_(s↓0) (H_s f-f)/s`.

**Forward implication.** Suppose `f ∈ Dom(A)`, and write `c_n = <f,e_n>`. For `s>0`, set
`q_s(w) = (exp(-s w)-1)/s`. For every `w≥0`,

`-w ≤ q_s(w) ≤ 0`, and `q_s(w) -> -w` as `s↓0`.

Thus `0 ≤ q_s(w)+w ≤ w`. Parseval and the diagonal heat formula give

`||(H_s f-f)/s - Af||² = sum_n |q_s(omega_n)+omega_n|² |c_n|²`.

Every summand tends to zero and is bounded above by
`omega_n² |c_n|²`, a summable majorant by `f ∈ Dom(A)`.
Dominated convergence for countable series proves

`lim_(s↓0) ||(H_s f-f)/s - Af|| = 0`.

Consequently `Dom(A) ⊆ Dom(G)` and `Gf = Af` there.

**Reverse implication.** Suppose `f ∈ Dom(G)` with right derivative `g`.
For each `n`, apply the continuous Hilbert-basis coordinate functional
`f ↦ <f,e_n>` to the strong derivative. Since the scalar derivative of the heat multiplier at zero is `-omega_n`,

`<g,e_n> = -omega_n <f,e_n>`.

Parseval applied to `g ∈ H` yields
`sum_n omega_n² |<f,e_n>|² = ||g||² < infinity`.
The *previously established exact spectral-domain equality* therefore implies
`f ∈ Dom(A)`; the diagonal formula also gives `Af = g`.

Hence

`Dom(G) = Dom(A)` and `G = A = closure(L_(lambda,0))`.

This establishes the desired generator identification as **equality of the unbounded operators including domains**, not merely agreement on polynomial eigenvectors.

## 4. Sharp mean-zero heat decay

Let `f ∈ H` satisfy `<f,e_0> = 0`. Since
`omega_n ≥ omega_1 = 1+2lambda` for every `n≥1`, Parseval yields for every `s≥0`

`||H_s f||² = sum_(n≥1) exp(-2s omega_n)|c_n|²
             ≤ exp(-2s(1+2lambda)) ||f||²`.

Taking square roots gives

`||H_s f|| ≤ exp(-s(1+2lambda)) ||f||`.

For `f=e_1`, the inequality is an equality for every `s≥0`; hence the spectral-gap exponential rate is sharp. The separate closed-domain Poincaré optimality theorem gives an equivalent gap witness at the quadratic-form level.

## 5. Historical Lean certification checklist (now discharged)

1. Prove the full-`L²` heat coefficient formula by finite-basis truncation, continuity of `H_s`, and the HilbertBasis expansion theorem.
2. Formalize the positive-time scalar bound and right derivative `(exp(-s*w)-1)/s -> -w` for `w≥0`.
3. Prove dominated convergence of the squared Hilbert-basis coefficients for every input in the *canonical closed graph domain*.
4. Prove the reverse implication via coordinate continuity and Parseval, then assemble the equality `Dom(G)=Dom(A)` and `G=A`.
5. Derive the all-`L²` mean-zero contraction with exact decay factor and prove equality on the degree-one normalized mode.
6. Compile and perform explicit `#print axioms` audits on each new theorem, tied to its exact commit SHA. Exclude `sorryAx` and `Lean.ofReduceBool` from the audit.

**Isolation:** V007 branch / PR #16 only. No merge into `main`; no changes to V097 or V170.


## 6. Historical Lean 4 certification frontier — earlier on 2 November 2026

This section records only individually checked GitHub Actions results on the V007 branch. A green workflow certifies declarations at its specific checked-out SHA, **not** arbitrary later edits or the still-unproved full domain equality.

- **Full weighted-real-L² strong Yosida heat limit:** [CI 41252264177](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41252264177), SUCCESS.
- **Contractive full-L² limit CLM:** [CI 41252657051](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41252657051), SUCCESS.
- **Positive-time semigroup identity:** [CI 41427396901](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41427396901), SUCCESS.
- **Full-L² strong C₀ continuity:** [CI 41428776506](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41428776506), SUCCESS.
- **Exact heat semigroup operator norm `‖H_s‖=1`:** new `UltrasphericalSturmLiouvilleRealHeatLimitExactNorm.lean` at commit `47167bf5`; [CI 41429860101](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41429860101), SUCCESS, with targeted axiom audit.
- **Right scalar slope `(exp(-s ω)-1)/s → -ω`:** `UltrasphericalSturmLiouvilleRealHeatScalarSlope.lean` at `d7d34307`; [CI 41430249990](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41430249990), SUCCESS.
- **Right slope on every actual normalized weighted-L² Gegenbauer eigenmode:** `UltrasphericalSturmLiouvilleRealHeatModeDerivative.lean` at `d3fc1406`; [CI 41430442037](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41430442037), SUCCESS.
- **Uniform scalar error majorant for `s>0, ω≥0`:** `0 ≤ (exp(-s ω)-1)/s+ω ≤ ω`, in `UltrasphericalSturmLiouvilleRealHeatScalarDomination.lean` at `3f982e16`; [CI 41431014583](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41431014583), SUCCESS.
- **Finite Gegenbauer core right derivative:** `UltrasphericalSturmLiouvilleRealHeatFiniteSpanDerivative.lean` at `66c4d1a0`, [CI 41431328861](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41431328861), IN_PROGRESS at this checkpoint. Do **not** count it as certified before SUCCESS.
- **Sharp closed-domain Poincaré constant:** [CI 41428064114](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41428064114), SUCCESS.
- **Compact canonical closed Sturm resolvent and sharp finite-rank truncation norm:** [CI 41429342198](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41429342198), SUCCESS.

**Remaining central operator theorem:** construct the full-L² heat-coefficient identity, prove norm convergence of the derivative quotients on `Dom(closure(L_{λ,0}))` using the just-certified scalar majorant and spectral square-summability, prove the converse inclusion of domains by coordinate continuity and Parseval, and conclude exact equality of the closed operator and the semigroup generator. Neither the eigenmode nor the finite-span derivative by itself establishes the domain equality.

## 7. Final generator theorem: exact Lean 4 certificates — 2 November 2026

The earlier open obligations in §§5–6 have now been discharged. Here are the exact checks, distinguishing mathematical implications from the source SHA and workflow that kernel-checked each statement:

| Theorem / scope | Verified GitHub Actions run | Result |
|---|---|---|
| `sturmRealClosed_graph_of_diagonal_coefficients`: the certified coordinate criterion for the actual closed Sturm graph | [41434260651](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41434260651) | SUCCESS |
| `sturmRealHeatLimit_right_derivative_repr`: coefficients of any strong right derivative | [41436992960](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41436992960) | SUCCESS |
| `sturmRealHeatLimit_generator_graph_subset_closedSturm`: reverse generator graph inclusion | [41438270476](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41438270476), source SHA `63dedea24377ea48a31a976ae32778f44cb89b96`, 9,125 jobs | SUCCESS |
| `sturmRealHeatLimit_closed_sturm_right_derivative`: full-domain strong right derivative, recompiled with the sqrt-zero correction | [41438637975](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41438637975), source SHA `ae52253f87b3a93410c0d6799f78b7e647e0daa4`, 9,128 jobs | SUCCESS |
| `sturmRealHeatLimit_generator_exact_closedSturm_graph` and `sturmRealHeatLimit_generator_graph_set_eq_closedSturm`: equivalence of derivative existence with canonical-domain membership and literal equality of the sets of ordered pairs | [41438637991](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41438637991), same source SHA `ae52253f87b3a93410c0d6799f78b7e647e0daa4`, 9,132 jobs | SUCCESS |

All final targeted CI jobs completed successfully; both last runs finished at 2026-11-02 11:47 UTC. The dedicated `#print axioms` output for each of the **two final graph theorems**, as well as the forward and reverse inclusion theorems, lists **only** `propext`, `Classical.choice` and `Quot.sound`. Both final workflows reject `sorryAx` and `Lean.ofReduceBool`; neither occurs in their accepted theorem audit.

**Precisely certified statement.** For each real `lam > 0`, and all `f, g : Lp ℝ 2 (measure lam)`, the strong right limit

`Tendsto (fun s : ℝ => s⁻¹ • (H_s f - f)) (𝓝[>] 0) (𝓝 g)`

holds if and only if there exists `x : (sturmRealPartialOperator lam hlam).closure.domain` whose underlying `L²` element is `f` and whose closed Sturm action is `g`. As a separate kernel-checked theorem, the two graph **sets** are exactly equal. Thus the infinitesimal generator `G_lam` of the actual `C₀` contraction semigroup and the canonical closure `A_lam = closure(L_lam,0)` agree *as unbounded operators including their domains*:

`Dom(G_lam) = Dom(A_lam)`, `G_lam f = A_lam f` on this common domain.

Proof directions:
- **Forward:** `UltrasphericalSturmLiouvilleRealHeatGeneratorClosedDomainForward.lean` uses the exact heat multiplier, a sharp uniform scalar bound, `tendsto_tsum_of_dominated_convergence`, and Hilbert-basis Parseval.
- **Reverse:** `UltrasphericalSturmLiouvilleRealHeatGeneratorReverseCoordinates.lean` transfers strong differentiation to continuous Fourier coordinates, then `UltrasphericalSturmLiouvilleRealHeatGeneratorReverseDomain.lean` invokes the exact canonical spectral-graph membership criterion.
- **Composition:** `UltrasphericalSturmLiouvilleRealHeatGeneratorExactGraph.lean` states and proves both the iff and set equality.

**Integrity check:** the five principal source files (`ClosedDomainForward`, `ReverseDomain`, `GraphBridge`, `ReverseCoordinates`, `ExactGraph`) have identical Git blob SHAs on the CI-certified `ae52253f` commit and the later observed PR head at the time of this audit. Later unrelated branch edits must not be construed as new CI certification of changed proof sources.

**Scope safeguard:** this settles the full weighted-real-`L²` Gegenbauer heat-generator identification. It does **not** automatically prove every other V007 claim involving the Fourier–Bochner transform, Gaussian Fock isometry or separate operator ideals. Keep PR #16 Draft/unmerged; do not alter `main`, V097 or V170.
