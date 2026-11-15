# MANUSCRIPTS 11–15 — Operator / Eulerian bridge audit

**Scope:** Manuscripts 11–14 as previously audited, plus the authoritative Manuscript 15 source of 13 November 2026 (30-page `15.tex`, SHA-256 `ccfcef205a7fc38db4386142a9173d0a8a60121ab58ae5ed1713f4219b1e200d`). The table below records the older historical cross-manuscript audit; the final addendum supersedes its stale M15 section attribution.
**Repository:** `ralfanop/Certifications_Eulerian_polar-curve_computations`.
**Purpose:** Dependency ledger for the distinct geometric, probabilistic,
operator-theoretic and numerical mathematical obligations. This is an audit
record, not a new theorem or a replacement for the manuscripts.

## Non-negotiable distinctions

- A source proof in a manuscript is not a Lean 4 formalization.
- A scalar Euler product is not by itself a Fredholm determinant of a
  specified trace-class Hilbert-space operator.
- A trace computed as a scalar spectral series is not automatically the
  abstract trace of an operator (nor the resolvent of an unbounded
  differential realization on `L²(0,1)`).
- A Mathlib `#print axioms` result and successful compilation apply to
  a particular exact commit SHA; a closed/merged PR alone does not prove
  what was checked.
- High working precision does not imply high certified interval accuracy.
- `j(z0)=j(z1)` does not imply `r_E(z0)=r_E(z1)`; the arguments in the
  numerical script `D(z0)` and the manuscript values `r_E(z0)` differ.

### Status keys

- **PROVED (Lean, exact head):** referenced relevant workflow checks have
  succeeded on the specified SHA; this does not imply all upstream
  physical identifications are formalized.
- **PROVED (Arb, exact head):** numerical interval statements only, after
  successful CI on the specified SHA.
- **CONDITIONAL:** existing source proof or stacked candidate must be
  reconciled with full exact-head CI and/or is conditional on another
  mathematical bridge.
- **OPEN:** a genuinely missing argument or formalization; not papered
  over by a scalar surrogate.

## Source connections and existing files

| Topic | Manuscript source | Existing Lean source or current PR | Audit status |
|---|---|---|---|
| Real Eulerian radius and sinc | M11; M12 §6; M15 | `EulerianCert.FourierModes.rE`; `lean/Manuscript15/EulerianCharacteristicIntegral.lean` | Source proof present; actual Fourier interval integral in Lean; **CONDITIONAL** as complete probability-law identification |
| Analytic complex Eulerian profile and duplication | M12 Definition 6.1 and Proposition 6.2; M14 §7 | `lean/SpecialImaginaryPoint/Section67ScalarCertificate.lean` (`rE`, `rE_two_mul`) | **CONDITIONAL** pending exact-head kernel/axiom trace for the full combined bridge |
| Characteristic function of centered uniform and law uniqueness | M11–M15 | `lean/Manuscript15/UniformProbabilityLaw.lean`, `EulerianCharacteristicIntegral.lean`, `CharacteristicMeasureUniqueness.lean` | Individual components present; end-to-end `ProbabilityMeasure.charFun` identification **OPEN** |
| `B(u)=(u-1)/log u`, `B(e^{iθ})=e^{iθ/2}r_E(θ)` | Flajolet–Sedgewick, *Analytic Combinatorics* (2009), III.25, IX.12, IX.35 | No exact complex logarithm / principal-branch bridge confirmed in existing sources | **OPEN**; must handle `θ=0` and branch of `Complex.log` |
| Eulerian histogram / Gaussian local limit | M11, M12, M15; Flajolet–Sedgewick IX.9, IX.14, IX.35 | `numerics/manuscript15_eulerian_7002_arb10000.py` | Finite exact integer arithmetic and interval checks are separate from a formal local limit theorem; latter **OPEN** |
| Universal true trace-class Fredholm determinant | M14 §6, M15 | `V14119Priority3UniversalFredholmExistence.lean`, `V14119Priority3UniversalFredholmEntire.lean` | Source present on main, in the certified dependency chain of #276/#277; **PROVED (Lean, exact heads below)** for their checked declarations |
| Local uniform convergence of derivatives and log derivatives | M14–M15 | `V14119Priority3FredholmCompressionDerivativesConverge.lean` | Part of certified #277 chain; not a trace-resolvent identity; **PROVED (Lean, exact head)** for its actual declarations |
| Joint trace-class / spectral determinant perturbation | M14–M15 | `V14119Priority3UniversalFredholmJointVariation.lean` | Source present in #277 certified chain; **PROVED (Lean, exact head)** for determinant perturbation only |
| Logarithmic derivative meromorphic and nonzero-domain differentiability | M14–M15 | `V14119Priority3UniversalFredholmLogDerivative.lean` | Source present in #277 certified chain; explicitly **does not** identify a resolvent trace |
| True diagonal Dirichlet inverse (ℓ² model) | M14 §6; M15 §2 | `V14119Priority3DirichletDiagonal.lean`, `V14119Priority3DirichletInverseFredholmDerivativeTrace.lean` | Positive nuclear diagonal model and derivative-at-zero spectral trace in #277 chain, **not** a differential `L²` realization |
| Explicit zero exclusion and stable log-derivative reduction | M14–M15 | Draft #278; Draft #280 | **CONDITIONAL** until all exact-head CI; remaining derivative difference estimate **OPEN** |
| Real Dirichlet Fredholm profile `sinh(x)/x` | M14 §6; M15 §2 | Stacked PR #270, #273, #275 | Candidate/source proof present; reconcile dependencies with current main before declaring end-to-end **PROVED** |
| Differential Dirichlet operators `A_1,A_2,A_DN` with genuine domains | M14 Definition 6.1; M15 Theorem 2.5 | Actual positive ℓ² Dirichlet inverse model exists; differential-domain equivalence not confirmed | **OPEN** |
| Unit equivalence `A_2 ≃ A_1 ⊕ A_DN` including domain transport | M14 §7; M15 §2 | None confirmed in the authentic differential-operator setting | **OPEN** |
| Fredholm determinant direct-sum factorization | M14 §7 | Scalar product identity in `Section67ScalarCertificate.lean` | **OPEN** as genuine operatorial direct-sum factorization |
| `d/dz log D_T(z)=Tr(T(I+zT)^{-1})` | M14 §6; M15 §2 | Holomorphic / log derivative formalized; not abstract trace-resolvent identity | **OPEN** (the primary analytic/operator bridge) |
| `2t Tr((A+t²I)^{-1})` and Langevin | M14 §§6–7; M15 | `Section67ScalarCertificate.lean` `TD`, `TDN`; `DirichletFredholmLangevinLogDerivative.lean` on #273 | Scalar series and real derivative formulas present; identification with genuine unbounded resolvent traces **OPEN** |
| Uniform positive-operator response stability `|L_T-L_S| ≤2x‖T-S‖₁` | M15 | No dedicated genuinely operatorial theorem confirmed | **OPEN** |
| Special values `z0=i/√2`, `z1=i√2`, `S z0=z1` | M14 §7; M15 | `Section67ScalarCertificate.lean` | Source Lean identities present; exact modular `j` value is separate |
| `j(z0)=j(z1)=8000` with true modular `j` | M14 §7 | No verified genuine Mathlib modular-`j` declaration found | **OPEN** |
| Special Arb points / real Eulerian duplication and traces | M11–M15 | Draft #281, `numerics/manuscripts11_15_eulerian_fredholm_bridge_arb10000.py` | **PROVED (Arb, exact head)**: strict interval signs, scalar enclosures, independent finite trace sums and integral-test remainder bounds; interval overlaps are *not* equality proofs |

## Verified GitHub commit-head CI evidence (12 November 2026)

- PR #276, SHA `1276c73049d88833e9f874b3c9a2c0144784a0c4`:
  35 workflow runs with conclusion SUCCESS; merged. This is the
  conflict-free Fredholm zero-divisor dependency track.
- PR #277, SHA `9668cf328a62c12906b99da2808e3cf395cf58b9`:
  41 workflow runs with conclusion SUCCESS; merged. This is the
  conflict-free operator compression and diagonal trace track.
- PR #281, SHA `20cdb49cdd958017e5c1807a38e63978e2d0d1de`:
  separate `push` and `pull_request` CI both SUCCESS. Pinned
  `python-flint==0.9.0`, 10000 Arb working bits, scalar minimum
  certified relative accuracy 9990 bits; finite spectral tails tested
  with independent integral-test upper bounds for N=8,32,128.
- PR #278 and PR #280 are dependent Draft tracks. They MUST be
  re-audited at their exact current heads before upgrading their
  statements from CONDITIONAL to PROVED.

## Priority DAG for independent agent cooperation

```
Classical Eulerian B(u) and centered uniform measure
     ├─> analytic complex profile r_E(z), duplication
     │      ├─> special z0,z1 evaluation and Arb #281
     │      └─> q_E(t)=sech(t), -d(log q_E)/dt=tanh(t)
     └─> convolution laws / histogram asymptotic (distinct limit-law proof)

Genuine CFC S₁ Fredholm determinant (#276/#277)
     ├─> meromorphic log derivative and derivative convergence
     │      ├─> operator trace-resolvent identity [OPEN]
     │      └─> quantitative derivative difference [OPEN]
     └─> joint operator/spectral perturbation
            └─> #278 robust zero exclusion
                   └─> #280 algebraic log-derivative bridge

Unbounded actual A1, A2, ADN on L² [OPEN]
     ├─> selfadjointness, positive resolvent trace class [OPEN]
     ├─> unitary reflection/even-odd decomposition [OPEN]
     └─> genuine determinant and resolvent trace factorization [OPEN]
            └─> operator derivation of Langevin duplication [OPEN]
```

## Allocation of work

A supporting numerical agent should own exact Arb interval work,
independent spectral truncations with stated rigorous tail estimates,
and the `B(e^{iθ})` analytic/probability-law interface, unless an
existing PR already supplies it. The separate operator-theory agent
should own the differential-domain, unitary decomposition, abstract
trace, and resolvent derivative chain. Avoid simultaneous edits to any
Draft PR's branch without coordination.

A verified interval *overlap* is **never** upgraded to an identity proof.
A successful finite-rank experiment is **never** upgraded to a
differential-operator direct-sum proof.

## Bibliographic provenance (not originality claims)

- P. Flajolet and R. Sedgewick, *Analytic Combinatorics*, Cambridge
  University Press (2009), esp. III.25, IX.12, IX.9, IX.14, IX.35:
  Eulerian numbers, local Gaussian limits, the function
  `B(u)=(u-1)/log(u)`, and uniform-sum connections.
- Classical Fredholm determinant theory, complex holomorphy,
  logarithmic derivatives, Sturm–Liouville spectral theory, and
  Euler sine/hyperbolic products: use the primary references in
  Manuscripts 11–15 before attributing priority.
- The mathematical manuscript-specific application of classical
  identities is separate from proof of its novelty.

**No merger authorization. No manuscript text modification.**


## 13 November 2026 — separate CURRENT M15 obligations from cross-manuscript research

**Authoritative manuscript:** `Manuscript_15_Editorial_Review_Maldacena2023_20261113/15.tex` (source SHA-256 `ccfcef205a7fc38db4386142a9173d0a8a60121ab58ae5ed1713f4219b1e200d`). The former §7 formal-certification table is gone; current §7 Discussion, §8 Open Problems, §9 Conclusions. This addendum updates *scope*, not previously successful SHA-bound CI evidence.

### Direct proof obligations for statements now in Manuscript 15

- §2.3 `prop:fourfold-eulerian`: independent integral identities (spherical/pure spin) and identification with specified Fredholm determinant; existing scalar spectral products are **not** an automatic full formalization.
- §2.4 `prop:two-eulerian-apices` and `lem:eulerian-triangle-fourier`: all-odd-n strict inequality, finite exceptional indices, analytic slope asymptotic *quoted from Manuscript 11*, and genuine Fourier series/derivative (off corners). The 7000 exact coefficient/peak Arb check does not prove these infinite claims.
- §2.6 `prop:laplace-unitime`: branch/domain assumptions for Laplace transform, matrix Cayley and Segal expression.
- §2.7 `thm:wasserstein`: the merged #287 finite Kantorovich precursors, tested head `1c8b2f887c720e178b315bf37ab0ccd4ec51a7b9` SUCCESS (#43461385180), are *finite sums only*; prove integrated couplings + W1 infimum independently.
- §3 `thm:rigidity`; §§4–5 cusp, curvature and terminal contact: full analytic-to-measure and local jet links remain distinct from existing characteristic/convolution Lean statements.

### OPEN cross-manuscript problems not to misidentify as M15 theorems

- Exact unitary equivalence of **unbounded differential** Laplacians with their authentic `L²/H²` domains and boundary conditions; scalar Fredholm product identities do not establish operator conjugacy.
- Abstract trace-resolvent logarithmic derivative and joint perturbation bounds beyond certified finite/scalar reductions.
- Authentic modular-j value `j(i/sqrt(2))=8000`; this is a **Manuscript 14** issue, not a current M15 theorem.
- Classical `B(e^{iθ})` branch continuation and general local limit connections may support the broader Eulerian programme; require explicit theorem citations before attributing them to current M15.

### Editorial and numerical audit

- The 2023 Maldacena *personal communication* bibliography entry is not cited in `15.tex`; do not fabricate what the private communication concerned. No source-manuscript edit has been made.
- The package contains no full source generator for Figure 1; do not promise exact vector path regeneration.
- Supplied Python script verifies finite rows n=3..15 and their 12-decimal angles with `mpmath`, not Arb. Its printed infinite-`n` angle limit is a mathematical statement quoted in the manuscript, **not established by script execution**. `numerics/manuscript15_eulerian_7002_arb10000.py` checks existing 7000 central probabilities; it must not be conflated with angle interval certificates. New claims require 10000-bit Arb, >=8182 certified relative bits, and SUCCESS on the exact tested SHA.
- Previous M15 §2 Fredholm comments in the historical table remain valid as cross-manuscript motivation but should not be interpreted as a statement that M15 has already proved differential-domain equivalence.

**No merge. No change to pinned Lean/Mathlib workflows. No new theorem or Arb certification asserted by this documentation-only addendum.**

### 13 November 2026 — new finite Table 1 Arb interval certification (exact head)

- [Draft PR #289](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/289), exact tested head `8c7cf91c4ac574659d5f11dcbc135a365e3f0b7e`, [workflow #43503120937](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43503120937), job `132153751280`: **SUCCESS**. The actual job log confirms `python-flint==0.9.0`, `ctx.prec=10000`, exact integer Eulerian recurrences, symmetry/normalization, rational mean/variance, and Arb intervals for **all 13 n=3,...,15 Table 1 central angles**. Every certified angle has **9996 relative bits** (threshold 8182). Each interval is strictly within the prescribed +/-0.5*10^-12 degree rounding cell, so the 12-decimal entries are certified. The small-index odd-angle equality n=3,5 and the finite n=7,...,15 slope inequalities are also checked exactly.
- **Limits:** This CI does **not** prove the all-odd-index strict inequality, asymptotic `alpha_n -> 180 degrees`, weak convergence, the 7000 vector Figure 1 drawing paths, or any Lean theorem. Those require separate analytic or geometric proof. This result is distinct from the existing Arb certification of 7000 *central probabilities*.
- Keep the PR Draft; **no merge**. Any new code edit requires another successful CI on that new head SHA.


## 15 November 2026 — current exact-head and integration audit (supersedes older status rows)

* [#309](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/309), head `e9fc982b75ad62f5dab8e17ab281fea2d71c65c6`, [CI #43695620183](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43695620183): **SUCCESS**, merged into main. The source `lean/Manuscript15/Section27PrimalWasserstein.lean` is present on main. Seven theorem audits use only propext, Classical.choice, Quot.sound: nonempty genuine probability couplings with prescribed pushforward marginals, finite-first-moment cost integrability, nonnegative primal infimum, Banach-valued Lipschitz integral bound, sharp complex phase chord estimate, actual Mathlib characteristic-function stability by |s| W1, and measure equality at zero distance. W1 here is defined by the standard unscaled infimum of integral costs. No optimal coupling or duality assumption. **Remaining §2.7:** explicitly compose with the manuscript's reconstruction coordinates and compact-time estimates; the full metric triangle inequality is not claimed by #309. This supersedes earlier statements that marginal identities and the primal infimum were still open.
* [#307](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/307), head `efdd3db6309cf30fc61b7c348b1a259e088db2ca`, CI #43659410661, and [#308](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/308), head `da5450e952015529fe15e82c16882dee28e8a170`, CI #43680178308: SUCCESS and merged into main; earlier infimum precursor statements have narrower scope.
* #291 head `37d4c42a80794c017ca0c836c5170a9006650468` CI #43581001519 and #43581001620 SUCCESS, merged: genuine measure-level Fourier transport and joint two-coordinate integrals. #288 head `d1be537b729b3f82285ccc3d8b7507153191c918` CI #43504421733 SUCCESS, merged: cycloid derivative/speed/curvature algebra and rational Cayley identities.
* #289 exact head `8c7cf91c4ac574659d5f11dcbc135a365e3f0b7e`, CI #43503120937 SUCCESS, merged: all 13 finite Table 1 angles n=3..15 have 9996 certified relative bits at 10000 working bits. #290 exact head `b061663621bd4d6e78142e882746d9648708dbef`, CI #43503214410 SUCCESS, merged: exact slopes s3=s5=2, s7=35/18 and strict N=10 scalar bound with minimum 9988 certified relative bits. Neither finite result certifies the general odd-n analytic inequality.
* **Integration distinction:** #185, #270, #273 and #274 were marked merged into intermediate base branches, not directly main. At the audited main SHA `421223108f3c26aa6e78730567a87e50e4846241`, the actual Dirichlet Fredholm sinh, Eulerian–Parry, all-real and Langevin derivative modules and the separate special-scalar Arb script were absent. Historical exact-head successes remain valid for the tested sources, not as main-branch integration evidence. #261 (old cast repair) was superseded mathematically by #185, CI #43234415908, with four standard-axiom theorems, but cannot be merged conflict-free. [Draft #312](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/312) restores the four Lean sources and Arb script from verified #273/#274, leaving existing matching dependencies untouched. Its head `61092226fa8996dc76f8981bba4fe9c5fb1c30b2` has new Lean CI #43699334222 and Arb CI #43699334286 pending at this checkpoint. Do not claim integrated certification until exact-head CI succeeds and the author merges the replacement. Close #261 only after verified replacement.
* Unbounded differential L² domain and resolvent-trace identification, general-law cycloidal rigidity, higher-order contact/cusp, geometric probability measures, global odd-order inequality, Fourier triangle and Laplace integral remain separately tracked obligations; see the 13 November Section 2 scope audit. No conclusion about physical conjectures is asserted.

This is documentation only. No new Lean/Arb certificate is claimed by the ledger commit itself; no code or manuscript is modified here. History remains available, and the above current status supersedes older pending/open statements where explicitly indicated. No merge authorized.
