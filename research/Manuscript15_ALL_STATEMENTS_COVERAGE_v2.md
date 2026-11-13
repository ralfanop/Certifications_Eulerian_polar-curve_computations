# Manuscript 15 — complete theorem-level Lean/Arb coverage matrix (revision e)

**Manuscript (current authority):** `Manuscript_15_Editorial_Review_Maldacena2023_20261113/15.tex` (13 November 2026, 30-page compiled PDF; SHA-256 `ccfcef205a7fc38db4386142a9173d0a8a60121ab58ae5ed1713f4219b1e200d`). Earlier theorem rows below are a historical snapshot of the 11 November version and are superseded where the 13 November addendum explicitly differs.
**Repository:** `ralfanop/Certifications_Eulerian_polar-curve_computations`.
**Status convention:** `kernel CERTIFIED` only after a successful exact-source run with #print axioms and permitted standard axioms; `Arb CERTIFIED` only for a *specific defined numerical expression* with a successful outward-enclosure check. A prose analytic proof is not automatically a formal proof.

| # | Manuscript result | Relevant source | Lean kernel coverage | Quantitative coverage | Remaining obligations |
|---:|---|---|---|---|---|
| 1 | Exact cycloidal reconstruction | Theorem 2.1, `thm:reconstruction` | X, Y, and kinematic identity kernel-checked in PR #112 | None required for functional identity | General library connection and numerical derivative/speed derivations |
| 2 | Speed and curvature realizations | `prop:curvature` | Reconstruction algebra only | None needed | Full differential/curvature theorem, cusp exclusions |
| 3 | Exact cycloidal–Fredholm–Langevin identity | `thm:fredholm` | Independent genuine universal Dirichlet Fredholm bridge, PRs #151, #159; needs declaration-level equivalence audit | Specializations numerically covered by Arb #179 | Exact translation of all displayed formulas and operator hypotheses |
| 4 | Special imaginary points | `cor:special` | Existing analytic/spectral dependencies; not counted as full M15 corollary | r_E(i/√2), r_E(i√2): Arb #179 | Formal complete corollary and branch conventions |
| 5 | Conformal Cayley half-angle chart | `prop:conformal` | Not certified in M15 | None | Explicit chart definitions, inverses and null-cone geometry |
| 6 | W₁ Lipschitz stability | `thm:wasserstein` | Abstract X and Y estimates submitted in PR #187 (CI pending); not full W₁ statement | No numeric values | Formal characteristic-function coupling / W₁ definition; compact-interval continuity |
| 7 | Rigidity of centred uniform law | `thm:rigidity` | `CoefficientRule` and its uniqueness kernel-checked (#112); c1–c7 kernel-checked (#115, #181) | No irrational constants required | Derive recurrence from analytic entire characteristic function; uniqueness of the measure |
| 8 | Exact leading cusp invariant | `prop:cusp` | Conditional leading algebra checked (#112) | None | Probability-law small-t expansion, rigorous limit |
| 9 | Compatibility and injectivity | `prop:compatibility` | Exact function-level compatibility, inverse and injectivity candidates PR #187 | No numerical values | Exact-head CI; measure uniqueness from characteristic function |
| 10 | Fourth-moment cusp expansion | `prop:cusp-fourth` | Arithmetic core PR #188 candidate | Exact rational moments; Arb unnecessary | Taylor remainder and quotient asymptotics |
| 11 | Universal leading cusp curvature | `prop:cusp-curvature` | No complete M15 formalization | None | Differentiation of asymptotics, curvature limit with sign |
| 12 | Convolution cusp / endpoint classification | `thm:convolutions` | Algebraic coefficient consequences PR #188 candidate | Exact integers/rationals; Arb unnecessary | rE^M derivatives at 2π; endpoint regularity; full cusp limit |
| 13 | Terminal contact order identifies convolution order | `cor:terminal-contact` | Not certified | None | Local analytic inversion, order-of-zero and derivative jet |
| 14 | Quadratic cusp correction for uniform sums | `cor:hierarchy-fourth` | Explicit fourth-moment and correction identities PR #188 candidate | Exact rational formulas | Independent uniform variables moment theorem and O(t⁴) remainder |

## Exact numerical layer

**PR #179, successful exact-source job:** [GitHub Actions #43080355596](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43080355596).
At `ctx.prec=10000`, all **14** evaluated nonzero real expressions achieved **9996–9998 certified relative bits**, strictly exceeding the **8182-bit** target. The Figure 1 annotation `α₃ ≈ 53.1301023542°` additionally passed the rounding-cell test. These are **certificates of the evaluated expressions only**, not of the asserted geometric or operator-theoretic interpretations.

## Formal proof semantics

`coefficientRule_c_four`–`coefficientRule_c_seven` in PR #181 passed exact-source [GitHub Actions #43080899625](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43080899625). They certify rational consequences conditional on `CoefficientRule`, **not** the proof that a probability law satisfying the kinematic identity must meet that rule.

## Additional non-theorem proof obligations

The numbered identities on area, Eulerian histogram, Plouffe/Sprugnoli inverse-binomial series, cone chart, endpoint order, higher derivatives, inverse moment extraction and physical research delimitations must be tracked at individual equation level. This matrix is an inventory of all **14 named theorem/proposition/corollary environments**, not an assertion that every mathematical statement is already formalized.

**Policy:** no changes to Manuscripts 11–14, V007 or V097; no unauthorized merges. Update this ledger only when CI outputs and the actual source declaration support an upgrade.


## Subsequent November 11 proof tracks

- PR #181: Lean coefficients c4–c7, exact-source kernel SUCCESS.
- PR #188: exact fourth-moment/cusp arithmetic, exact-source kernel SUCCESS.
- PR #202: exact integer mass/positivity/symmetry for every Eulerian profile n=3,…,7002 plus eight 10000-bit Arb peaks, exact-source SUCCESS (9998 certified relative bits).
- PRs #187, #191, #193, #200, #203, #204, #206, #208, #209: independent draft statements and workflows; CI results must be inspected before marking their declarations certified.

This appendix reports the verified state at its creation; consult the actual PR exact-head CI for later updates. In particular the nominal 10000-bit work precision is not itself an accuracy certificate.

## November 12, 2026 — actual Eulerian convolution law, uniqueness and order separation

The following are **exact-source Lean 4 kernel certifications** for genuinely defined
Borel probability measures, not merely formal scalar Fourier identities.

| PR | Declaration group and exact scope | Verified workflow | Result |
|---|---|---|---|
| [#229](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/229) | Actual n-fold additive convolution of the centered uniform measure is a probability measure for every n≥0, with `charFun(μ_E^{∗n})(t)=(r_E(t):ℂ)^n` | [#43225043204](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43225043204) | SUCCESS |
| [#258](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/258) | Injectivity of characteristic-function identification among finite Borel measures from an arbitrary dense frequency set, including the countable rational frequencies | [#43228552263](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43228552263) | SUCCESS |
| [#266](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/266) | Every two distinct convolution orders give distinct actual probability measures; their Fourier values at t=π are (2/π)^n | [#43233510728](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43233510728) | SUCCESS on tested commit |
| [#267](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/267) | Strict decrease of the real characteristic Fourier sample at t=π, and geometric convergence to zero as n→∞ | [#43234288162](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43234288162) | SUCCESS |
| [#268](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/268) | For every n≥0, existence and uniqueness of a genuine Borel probability measure with exact sinc-power characteristic data, even if specified only at all rational frequencies | [#43235071879](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43235071879) | SUCCESS |

**Theorem-scope interpretation.** These results close the *measure existence and
Fourier-uniqueness* obligations for the **specific pre-identified uniform
convolution family** and establish one-frequency identifiability of its
natural-number convolution order. They do **not** establish that a general
cycloidal kinematic/functional equation forces an arbitrary competing
measure to have this Fourier profile. They also do **not** certify the
Manuscript 15 terminal endpoint contact-order jet/cusp theorem, its
higher-order remainder, or the differential-geometric curvature theorem;
those remain separate proof obligations. The fixed-frequency limit of
`charFun μ_E^{∗n}` at t=π is **not** a weak convergence theorem for
`μ_E^{∗n}` without rescaling.

This entry reports exact witnessed workflow conclusions and mathematical
scope. It does not assert that later PR merges or updates retain the exact
same tested source SHA without additional verification.


## November 12, 2026 — exact-head follow-up: terminal jets, Fourier transport and Arb

The following checks use the *actual PR head SHA*, not the target-branch SHA.
A successful workflow establishes only what its compiled Lean declarations and
numerical script assert, not automatic equivalence with every manuscript statement.

| PR | Exact PR head | Workflow / conclusion | Audited scope |
|---|---|---|---|
| [#236](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/236) | `f743c86ed693206f239d47b3bbac7ce2280a1152` | [#43192558071](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43192558071), SUCCESS | Composed convolution terminal derivative declarations; the complete analytic local-inversion/contact-order corollary remains a separate obligation. |
| [#240](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/240) | `64c156b6ffef772b2f61ea2c92275d0dc6f3034b` | [#43193085525](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43193085525), SUCCESS | Sharp cosine/sine Fourier phase transport bounds; not by itself a full Wasserstein-1 theorem. |
| [#242](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/242) | `bb5ac12cfb961890eca2a986240d048c789664ad` | [#43221740185](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43221740185), SUCCESS | Actual uniform-law characteristic and moment integrals; not a derivation of the cycloidal rigidity equation from an arbitrary law. |
| [#274](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/274) | `d906249d7ec8e68cc1372590a6564756f0373b19` | [#43260765343](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43260765343), SUCCESS | Separate 10000-bit Arb workflow for Fredholm–Langevin special scalars; the exact enclosure/accuracy inventory must be read from its script and logs before claiming a number of certified expressions or a minimum achieved accuracy. |
| [#273](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/273) | `b4dab696191d9e076948e97ace55b63d76e2de5d` | [#43276238484](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43276238484), IN PROGRESS at inspection | Candidate true-operator Fredholm logarithmic derivative / spectral trace; **not yet certified**. |

These rows supersede stale `CI pending` language **only for the exact
declaration groups indicated**. In particular, do not promote manuscript
Theorems 6, 7, 12 or 13 to complete certification merely because a supporting
workflow succeeds. The established 8182-bit threshold remains mandatory for
every newly claimed nonzero Arb enclosure. No figure or earlier manuscript
is modified by this ledger update.

## November 12, 2026 — verified completion of pending exact-head audits

This section updates, rather than silently rewrites, the earlier point-in-time rows.

* **PR #273**, exact head `b4dab696191d9e076948e97ace55b63d76e2de5d`: [workflow #43276238484](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43276238484) is now **SUCCESS**. The job specifically completed compilation of the genuine Fredholm logarithmic derivative/Langevin spectral-trace identities and the four-theorem kernel axiom audit. This supersedes the earlier “IN PROGRESS” status for that SHA only. It does not certify unrelated terminal-contact or rigidity statements.
* **PR #274**, exact head `d906249d7ec8e68cc1372590a6564756f0373b19`: [workflow #43260765343](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43260765343), job `131331096672`, is **SUCCESS**. The execution log explicitly reports `ctx.prec: 10000`, twelve nonzero outward Arb interval values, and *certified relative bits* individually equal to 9997, 9997, 9996, 9996, 9990, 9992, 9991, 9993, 9990, 9992, 9991, 9990. Thus the observed **minimum is 9990 certified relative bits**, exceeding the required 8182. The twelve values are `a`, `b`, `D(a)`, `D(b)`, `Dprime(a)`, `Dprime(b)`, `L(a)`, `L(b)`, `V(a)`, `V(b)`, `D(b)-D(a)`, and `L(b)-L(a)`. Strict-sign and interval-overlap checks passed. Interval overlap is a numerical consistency test, not an independent exact symbolic proof.
* **PR #276**, exact head `1276c73049d88833e9f874b3c9a2c0144784a0c4`: 35/35 associated pull-request workflow runs report SUCCESS. **PR #277**, exact head `9668cf328a62c12906b99da2808e3cf395cf58b9`: 41/41 report SUCCESS. The preceding failed universal-compression audit had compiled `V14119Priority3FiniteCompressionTwoFamilyBound.lean` but demanded an axiom report from `V14119Priority3UniversalCompressionTraceNorm.lean`; the subsequent CI correction compiled the actual target. These two PRs are supporting Manuscript 14 operator-theory infrastructure, **not** evidence that every Manuscript 15 theorem is closed.
* The exact-head PR #236 (15/15 runs), #240 (1/1 run), and #242 (15/15 runs) also show only successful associated pull-request workflow runs. These counts are the first-page commit-associated API results and do not replace a per-declaration theorem-scope audit.

**Outstanding mathematical gaps:** a general-law-to-cycloidal-rigidity implication, full higher-order terminal-contact/cusp jet, differential curvature classification, and the measure-level integrated Wasserstein-1 stability theorem beyond the certified phase-transport kernel. None is promoted to certified here.

This is a documentation-only update. No manuscript, figure, V007/V097 source, numerical script, or Lean proof is modified; no merge is requested.


## November 12, 2026 — exact-head follow-up on joint Fredholm perturbations

The following observations were obtained from the pull-request-associated GitHub Actions runs on the **specified head SHA**. They do not assert that the parent dependencies are merged into `main`.

| PR | Exact head SHA | Workflow outcome | Precise interpretation |
|---|---|---|---|
| [#278](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/278) | `e1916a3ffa8b1e4a8458944c91a6098b608ea750` | 1/1 SUCCESS | Lean proof of robust zero-exclusion under joint trace-class/operator and complex-parameter perturbations, conditional on the imported universal Fredholm variation estimates. This is a supporting nonvanishing result, not a full M15 stability theorem. |
| [#280](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/280) | `efef5e7cca1439b9ae003be8edd4a37919f2460b` | 2/2 SUCCESS | Algebraic logarithmic-derivative stability *reduction* on nonzero denominators. The required unconditional trace-norm bound for the derivative numerator is **not** established by this reduction. |
| [#284](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/284) | `eb11017760a77349295417cd5c01638cd4bee9b2` | [workflow #43313143479](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43313143479) IN PROGRESS at inspection | Candidate scalar reflection-interface value and first-derivative matching identities. No certification claim until exact-head CI succeeds; no assertion of H² domain gluing or operator conjugacy. |

The independent Arb precision policy remains `ctx.prec=10000` with rigorously checked certified relative accuracy at least **8182 bits** for each claimed nonzero enclosure. No new Arb numerical certificate is claimed by this appendix. PRs #236, #240 and #242 retain their previously recorded exact-head successful workflow outcomes. The full M15 general rigidity, higher-order terminal-contact, differential curvature, and integrated Wasserstein-1 obligations remain open.

No manuscript, figure, V007/V097 file or theorem source is changed in this ledger-only commit; no merge is authorized.


## November 13, 2026 — exact-head reflection-interface proof check

* **PR #284**, exact head `3c18fb6548c7f19f3a87cb2138028732ba784f9b`: [GitHub Actions run #43348629889](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43348629889) completed with **SUCCESS**. This supersedes the earlier in-progress entry for `eb11017760a77349295417cd5c01638cd4bee9b2`. The draft proves scalar reflection-interface trace algebra and matching criteria; it does **not** prove Sobolev H² domain gluing, unitary L² transport, or differential-operator conjugacy. No Manuscript 15 rigidity, contact-order, curvature, or Wasserstein-1 theorem is promoted by this supporting result.
* Independently rechecked exact heads for PRs #236 (`f743c86ed693206f239d47b3bbac7ce2280a1152`, 15/15 successful workflow runs), #240 (`64c156b6ffef772b2f61ea2c92275d0dc6f3034b`, 1/1), and #242 (`bb5ac12cfb961890eca2a986240d048c789664ad`, 15/15). The API exposes the first page of commit-associated pull-request runs; the result is not an assertion about every possible historical run.
* PRs #278 (`e1916a3ffa8b1e4a8458944c91a6098b608ea750`, 1/1), #280 (`efef5e7cca1439b9ae003be8edd4a37919f2460b`, 2/2), and #281 (`20cdb49cdd958017e5c1807a38e63978e2d0d1de`, 1/1) also retain successful exact-head workflow outcomes. The numerical working-precision requirement remains 10000 bits with a rigorously checked minimum of 8182 relative bits; workflow success alone does not establish a new numerical enclosure inventory.

Documentation only. No Lean theorem, Arb script, figure, manuscript, V007 or V097 source changed. No merge authorized.


## November 13, 2026 — latest exact-head revalidation

* **PR #284** now points to `0aa1d7d74578c7a69072133de9bd50e313b843d3`; its [workflow #43355543736](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43355543736) completed **SUCCESS** on this exact commit. This supersedes the earlier tested head `3c18fb6548c7f19f3a87cb2138028732ba784f9b`. Certification scope remains scalar reflection seam trace algebra only: no Sobolev H² gluing, unitary transport or unbounded differential-operator conjugacy is inferred.
* Revalidated the **actual PR heads** of #236 (`f743c86ed693206f239d47b3bbac7ce2280a1152`, 15/15 first-page runs SUCCESS), #240 (`64c156b6ffef772b2f61ea2c92275d0dc6f3034b`, 1/1 SUCCESS), and #242 (`bb5ac12cfb961890eca2a986240d048c789664ad`, 15/15 SUCCESS). These remain scoped supporting results, not full M15 theorem certification.
* No new Arb interval certificate is asserted here. The operational requirement remains 10000-bit Arb precision and at least 8182 rigorously verified relative bits for each newly claimed nonzero interval. General cycloidal rigidity, terminal higher-order contact, differential curvature and integrated Wasserstein-1 remain open.

Documentation-only; no merge and no modifications to manuscripts 11–14, V007/V097, figures, Lean proofs or Arb scripts.


## November 13, 2026 — current reflection-interface head audit

* **PR #284** advanced to exact head `c99057878a3b04c692354dd5b494bf22ec7a7181`. The associated [GitHub Actions run #43370677606](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43370677606) completed **SUCCESS**. This supersedes the earlier `0aa1d7d74578c7a69072133de9bd50e313b843d3` head check. The workflow is titled *Manuscripts 14–15 — reflection interface jet conditions*; passing it establishes successful execution of that workflow, not a proof of Sobolev H² gluing or unbounded-operator equivalence without separate statement-level inspection.
* Exact-head checks reconfirmed #236 `f743c86ed693206f239d47b3bbac7ce2280a1152` (15/15 first-page runs SUCCESS), #240 `64c156b6ffef772b2f61ea2c92275d0dc6f3034b` (1/1), and #242 `bb5ac12cfb961890eca2a986240d048c789664ad` (15/15). These do not close the outstanding M15 rigidity, higher terminal contact, curvature, or integrated Wasserstein-1 statements.
* No new Arb interval certification is inferred. Any new nonzero enclosure must use 10000-bit working precision and prove at least 8182 relative bits. No merge or manuscript/figure/source modification is authorized by this audit.


## November 13, 2026 — exact-head finite Fourier marginal transport audit

* **PR #286**, exact head `24d1f82a7d49546b16b698a3a1fc31e9bc6f9f00`: [workflow #43412912317](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43412912317) completed **SUCCESS**. The patch introduces `Manuscript15.finite_weighted_cosine_marginal_transport` and `Manuscript15.finite_weighted_sine_marginal_transport` in `lean/Manuscript15/FiniteFourierCoupling.lean`, reducing marginal differences to previously formalized nonnegative weighted phase-transport estimates. The dedicated workflow explicitly checks these declarations in the Lean output. This certifies the **finite weighted sum** statements on that tested SHA, not the integrated coupling or Wasserstein-1 infimum step.
* The historical exact heads of PRs #236 (`f743c86ed693206f239d47b3bbac7ce2280a1152`), #240 (`64c156b6ffef772b2f61ea2c92275d0dc6f3034b`), and #242 (`bb5ac12cfb961890eca2a986240d048c789664ad`) were independently queried again: respectively 15/15, 1/1 and 15/15 associated first-page pull-request workflow runs were completed with SUCCESS. These are **historical tested commits**; the status of any newer merged default-branch composition is a separate check.
* No new Arb calculation or accuracy claim is made here. Future nonzero interval claims require `ctx.prec=10000` and individually checked certified relative accuracy of at least 8182 bits. Higher-order terminal contact, general cycloidal rigidity, differential curvature, and the integrated Wasserstein-1 theorem remain open.

This appendix changes only the draft certification ledger. No merge, manuscript, figure, V007/V097, Lean proof or Arb script is modified.


## November 13, 2026 — exact-head finite Kantorovich test audit

* **PR #287**, exact head `6f904daed452f9a977c88b8eb2e4ef1b7ce1d4fd`: [workflow #43437777480](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43437777480) completed **SUCCESS**. The file `lean/Manuscript15/FiniteKantorovichTest.lean` contains four finite-coupling statements: `finite_lipschitz_test_marginal_transport`, `finite_unit_lipschitz_test_marginal_transport`, `finite_lipschitz_test_marginal_transport_global`, and `finite_unit_lipschitz_zero_cost_marginals`. The workflow compiles the file and checks the axiom audit output, rejecting `sorryAx` and errors. These are finite nonnegative weighted test-function inequalities, **not** an integrated coupling theorem or a Wasserstein-1 infimum theorem. PR #287 remains open and draft.
* Exact historical head checks reconfirmed PR #236 (`f743c86ed693206f239d47b3bbac7ce2280a1152`, 15/15 first-page associated runs SUCCESS), #240 (`64c156b6ffef772b2f61ea2c92275d0dc6f3034b`, 1/1) and #242 (`bb5ac12cfb961890eca2a986240d048c789664ad`, 15/15). These PRs have been merged, but the cited checks refer to their historical head commits, not a fresh default-branch integration build.
* Outstanding: prove the integral inequality for arbitrary coupling with integrability hypotheses, then take the infimum over transport costs; separately, general cycloidal rigidity, higher terminal contact and curvature classification remain open. No new Arb certificate is claimed: require 10000-bit working precision and at least 8182 rigorously verified relative bits for each new nonzero enclosure. No merge or changes to manuscripts 11–14, V007, V097 or figures.


## 13 November 2026 — authoritative 30-page Manuscript 15 revision (superseding older section inventory)

**Source of truth:** the user-supplied archive `Manuscript_15_Editorial_Review_Maldacena2023_20261113(1).zip`, `15.tex` SHA-256 `ccfcef205a7fc38db4386142a9173d0a8a60121ab58ae5ed1713f4219b1e200d`. This audit is anchored to that exact file and does not edit it.

**Editorial changes relative to 11 November `15.tex`:**
- Old §7 *Formal certification and open problems* was **removed as a standalone certification table**. Current §7 is *Discussion*, §8 *Open Problems*, and §9 *Conclusions*. Do not infer missing mathematical proofs from the deleted status table.
- Four new scoped statements in §2: `prop:fourfold-eulerian` (Fourier / Fredholm / sphere / pure-spin integral representations), `prop:two-eulerian-apices` (odd apex-angle classification), `lem:eulerian-triangle-fourier` (triangular Fourier profile and derivative), `prop:laplace-unitime` (Laplace/Cayley/Segal half-angle identities). These must have **separate** Lean theorem-level coverage; scalar algebra alone does not establish all integral/operator interpretations.
- The bibliography has 32 `\\bibitem` entries (up from 24). `maldacena-personal2023` is present in the bibliography but has no `\\cite` in the source. It is not appropriate to invent a mathematical attribution or attach a citation without substantiating the 2023 private correspondence. No unresolved citation keys were found by parsing comma-separated keys.
- Data/Code Availability now accurately state that the complete original Figure 1 generator is **not included**. Do not claim identical regeneration of its 7000 vector paths from the archive; a separate repository script verifies Eulerian coefficients and peak probabilities, not those paths.
- The AI declaration is different; that is an authorial editorial matter, not a Lean/Arb mathematical obligation. No unsupported restoration of deleted text was made.

**Revised scope and priority (current sections; do not duplicate existing PRs):**

| Current section | Enunciation / evidence | Remaining formal obligation |
|---|---|---|
| §2.3 `prop:fourfold-eulerian` | New four-representation proposition | Verify each integral normalization, equality to the analytic continuation, and honest relationship to the *specified* trace-class Fredholm determinant; compare against #273/#276/#277/#281 before adding proofs |
| §2.4 `prop:two-eulerian-apices` | Exact small odd equality n=3,5 and all odd n≥7 strict inequality | Existing 7000-row numerical tests are not an all-orders theorem; formalize the analytic inequality/positive-integrand majorants and the separately quoted asymptotic with proper M11 dependency |
| §2.4 `lem:eulerian-triangle-fourier` | Explicit piecewise-affine periodic function | Lean Fourier coefficient/integrability/convergence proof and differentiation away from corners, not merely checking finite values |
| §2.6 `prop:laplace-unitime` | New Laplace/Cayley/Segal formula | Formalize domain and branch hypotheses, the actual integral and matrix identity; avoid attributing physical equivalence |
| §2.7 `thm:wasserstein` | Six finite-coupling precursor statements in merged PR #287, exact tested head `1c8b2f887c720e178b315bf37ab0ccd4ec51a7b9`, run #43461385180 SUCCESS | Coupling integral, finite-first-moment integrability and infimum over couplings remain; finite sums alone are insufficient |
| §3 `thm:rigidity` | Measure existence, characteristic identification and convolution orders supported by earlier Lean PRs | General compact-support hypothesis => analytic functional equation => unique uniform law (full chain) |
| §§4–5 | Cusp/curvature/terminal order, with existing partial PRs | Higher-order jets, curvature hypotheses, exact terminal local inversion: declaration-by-declaration audit remains necessary |
| M14/M15 operator-bridge *research* | Differential-domain reflection, H² gluing, abstract trace-resolvent, modular-j | Keep in the cross-manuscript operator ledger; do not falsely label as currently claimed M15 theorem proofs |

**Reproduction classification:** the supplied `verify_eulerian_angles_n3_15_and_limit.py` has SHA-256 `afb60d7b162a89955a6c4d54c4d79e899cbf8e236b59f0c840d69e5efe550839`; local execution reproduced all **13 finite** tabulated angles n=3..15 to 12 decimals, with exact integer Eulerian recurrence, exact rational moment checks and 80-decimal-digit `mpmath` evaluation. The terminal printed assertion `alpha_n -> 180 degrees` is **not** a programmatically proved asymptotic. Neither 80-digit `mpmath` nor agreement at 12 decimals is an Arb interval certificate. Separate `numerics/manuscript15_eulerian_7002_arb10000.py` already checks all 7000 central peak probabilities using pinned python-flint and must not be duplicated for those same observables. For newly certified nonzero angles, require Arb working precision 10000 bits, >=8182 checked relative bits, a strict <0.5e-12-degree containment against the 12-decimal target, and a SUCCESS job on the **exact branch head SHA**.

**Status hygiene:** prior ledger text saying PR #287 is open/draft is historical; the PR was subsequently merged. No present document-only commit certifies any new Lean theorem or numeric result. No merge authorized.
