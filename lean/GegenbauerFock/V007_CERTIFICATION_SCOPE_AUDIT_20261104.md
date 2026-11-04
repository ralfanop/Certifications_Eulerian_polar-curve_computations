# V007 — Lean certification scope and manuscript comparison (4 November 2026)

**Status:** bounded, evidence-based audit of the V007 research draft against GitHub PR #16.  
**Repository:** `ralfanop/Certifications_Eulerian_polar-curve_computations`.  
**Branch:** `gegenbauer-fock-formalization-20261025`, PR [#16](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/16) (OPEN, DRAFT, DO NOT MERGE).  
**Manuscript snapshot compared:** `V007.2.tex` in the author's file Library, labelled 31 October 2026. The manuscript was **not modified** during this audit. A later manuscript revision, if any, must be compared separately.

## Evidence rules

- **CI verified:** successful GitHub Actions run inspected on the exact commit SHA. The statement must be interpreted literally as its Lean source enunciates; compilation alone does not establish mathematical novelty.
- **Source located:** relevant code/theorem exists in PR #16, but this audit did **not** independently verify its exact theorem's latest CI log. This is neither a failure nor permission to call the whole manuscript certified.
- **Open or not established:** no corresponding general theorem has been identified and independently checked in the scope claimed by the manuscript; distinguish from narrower certified claims.
- CI checks are version-specific. A repository-wide status cannot be inferred from one green workflow, and `#print axioms` audits only the declarations actually printed.

The draft's older `README.md`, `ANALYTIC_AUDIT.md`, `V007_HILBERT_PROOF_DOSSIER.md` and `V007_DOCUMENTO_DI_PASSAGGIO.md` preserve **historical October 2026 snapshots**. Claims in them that no concrete Fock operator, Gamma-normalized moments or exact Sturm generator have been formalized are now out of date; do not cite those historical paragraphs as present-tense statements.

## Crosswalk from V007.2 manuscript to proof artifacts

| Manuscript claim or topic | Lean source / audit evidence | Status and important scope |
| --- | --- | --- |
| §2 ultraspherical law, Gamma density and all monomial moments | `UltrasphericalGammaAllMoments.lean`, `UltrasphericalGammaKummerComplete.lean` | **Source located:** actual real Gamma-weighted integral identities for all degrees, with `lambda>0`. Fresh independent exact-CI verification of these specific modules remains outside this audit. |
| §2 Eulerian Fourier/Bessel and four-dimensional Catalan specializations | `EulerianFourierIntegral.lean`, `UltrasphericalGammaAllMoments.lean`, other named Bessel/Catalan modules | **Source inventory only:** individual specializations and dimension bridges must be matched to exact declarations before claiming manuscript-level coverage. |
| §3 complete Gegenbauer Hilbert spectral basis and canonical Sturm closure | `UltrasphericalSturmLiouvilleMonicRealL2HilbertBasis.lean` and closed-Sturm/spectral-realization modules | **Supporting formalizations exist.** The exact-generator graph identity is independently **CI verified** in [#41439924141](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41439924141), SUCCESS. The whole §3 was not reaudited line by line here. |
| §3 compact real resolvent / spectrum | Actual real Sturm resolvent modules and `V007_DOCUMENTO_DI_PASSAGGIO.md` §30 | **Certified milestones recorded** by the repository. The spectrum and truncation statements require their individual run IDs, not the unrelated heat or trace-class certificates. |
| §4 genuine analytic Bargmann–Fock operator | `GegenbauerIntrinsicEntireFockOperator.lean` | **Source located:** `C_intrinsicEntire` is defined as an actual bounded map into the entire Gaussian L² submodule, via the coefficient-space equivalence. This contradicts the old README claim that only a sequence model exists. Its current CI was not independently checked in this audit. |
| §4 exact Hilbert–Schmidt/Kummer energy and Gram trace | `GegenbauerIntrinsicEntireHSKummer.lean` | **Source located:** `C_intrinsicEntire_HS_energy_eq_kummer`, `C_intrinsicEntire_Gram_basis_trace_eq_kummer`, other exact source-basis statements. Verify their own exact CI before labelling the paper's full analytic theorem certified. |
| §4 explicit adjoint/evaluation at the imaginary segment | `AdjointBasis.lean`, `GegenbauerIntrinsicEntireGramPairing.lean`, `GegenbauerIntrinsicEntireBochnerEvaluation.lean` and related modules | **Source inventory only.** Separate coefficient-space adjoint, analytic evaluation, complex conjugation and a.e. identification. Do not equate them without checking the exact theorem types. |
| §5 factorial finite-rank tail, all Schatten classes and zero spectral point | Numerous `InfiniteFockTruncations`, `GegenbauerIntrinsicEntireGram*`, `PhyslibTraceClass*` modules | **Multiple formalizations available**, but the composite statement “all S_p for p>0” must be checked for the actual operator and for the same ideal definition. No blanket certification recorded here. |
| §6 spheroidal exponential-kernel balance | `SpheroidalExponentialBispectral.lean` | **Source located:** true first/second real derivatives and the *pointwise* identity (L_u e^{cuv}=L_v e^{cuv}). **Not** by itself a domain-invariant commutation of unbounded closed operators. |
| §7 Cohl/Funk–Hecke angular multipliers and Green comparison | V007.2 text; `V007_SPHEROIDAL_COMMUTATION_PROOF.md` and other mathematical dossiers | **Not established by this audit:** no matching source filename for a full normalized Funk–Hecke theorem was found among PR changed modules; this does **not** prove that no theorem exists under a different name. Do not claim Green resolvents equal the Gaussian Gram operator. |
| §8 rational enclosure and analytic tail | `RationalTrace.lean`, `RationalTraceAnalyticTail.lean`, `GegenbauerIntrinsicEntireHSRationalEnclosure.lean` | **Source located:** rational and analytic-tail developments exist, superseding old “finite arithmetic only” notes. Verify the exact rational interval and remainder hypotheses against the paper and the individual CI. |
| §9 Lean/Arb certification ledger | This audit plus `V007_REAL_HEAT_GRAPH_NUCLEAR_S1_CERTIFICATION_20261104.md` | **Partially refreshed.** Numerical Arb certificates are an independent evidence layer and cannot be replaced by a Lean source file or vice versa. |
| Operator-theoretic extension: actual closed real heat semigroup and sharp real nuclear cost | `UltrasphericalSturmLiouvilleRealHeatGraphNuclearExactS1Certificate.lean` | **CI verified:** [#41805555379](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805555379), SUCCESS. The joint theorem covers graph-norm continuity, compactness and the exact *real projective nuclear infimum* for (s>0), not (s=0). |
| Real heat versus complex CFC trace norm under matching-spectrum hypotheses | `UltrasphericalSturmLiouvilleRealHeatComplexCFCS1Bridge.lean`, `RealComplexPositiveSpectralAutomaticTraceClassBridge.lean` | **Conditional bridge source located:** for a positive complex operator with a complete orthonormal eigenbasis carrying exactly the heat eigenvalues, the source constructs its complex CFC trace-class witness and equality with the real heat projective nuclear infimum. A second variant assumes an actual basis-preserving real-linear intertwiner. Neither proves that an arbitrarily selected complex Gegenbauer–Fock Gram is that operator. No new exact-CI audit of this module was made here. |
| Complex source/output Gegenbauer–Fock Gram norms | `PhyslibDualGramsActualS1NormEquality.lean` | **Source located:** trace-class source/output Gram norms agree and equal the Kummer mass; this is a complex-space statement distinct from the real nuclear heat norm. No fresh module-specific CI audit here. |
| Operator-theoretic extension: true complex trace-class coisometric splitting and numerical subspace gap | `PhyslibTraceClassCoisometricCoordinateStability.lean` | **CI verified:** [#41804414349](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804414349), SUCCESS, with 35 `#print axioms` audits. Includes `min(1,4‖U−V‖)` for the real-valued normalized gaps of ranges and kernels, and convergence under operator-norm limits of coisometries. This is an S₁ stability theorem, **not** an identification with the independently built real projective nuclear norm. |

## Verified recent milestones and exact-run boundaries

The following GitHub Actions **run conclusions were queried directly** on 4 November 2026:

| Run | SHA (first 8 chars) | Conclusion | Evidence class |
| --- | --- | --- | --- |
| [#41439924141](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41439924141) | `3781e802` | SUCCESS | Generator graph equality with canonical closed Sturm operator |
| [#41717492441](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41717492441) | `cda2078d` | SUCCESS | Numerical real `sSup/sInf` subspace gaps |
| [#41803582930](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41803582930) | `7c18ceb4` | SUCCESS | Uniform `min(1,4‖U−V‖)` gap bound |
| [#41804414349](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41804414349) | `45cfb4dd` | SUCCESS | Current-source coisometric split convergence/gap limit |
| [#41805396014](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805396014) | `132823f7` | SUCCESS | Real nuclear rank-one series implies compactness |
| [#41805555379](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805555379) | `a3550a24` | SUCCESS | Closed-graph, compact, exact real heat nuclear S₁ joint certificate |
| [#41805914469](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805914469) | `aae09909` | SUCCESS | Exact real nuclear norm of a **given** two-partial-orthonormal-family singular expansion |

For detailed theorem-by-theorem axiom logs, use the run's actual job log. The above table establishes the run conclusions; earlier source-audit checkpoints document the printed axioms of the coisometric and heat certificates.

## Priority open proof boundaries

1. **General real singular value theory — highest substantive remaining bridge.** `RealNuclearPartialSingularFamilyS1Exact.lean` assumes the actual rank-one expansion (T=sum_n sigma_n,c_notimes b_n) for two possibly incomplete orthonormal families. It correctly proves the universal exact real projective nuclear cost *conditional on that expansion* (CI #41805914469). It does **not** construct (|T|=(T^*T)^{1/2}) and the partial-isometry singular decomposition for every compact real Hilbert-space operator, nor prove the global “nuclear iff summable singular values” equivalence. See `V007_REAL_S1_PARTIAL_ISOMETRY_COMPLETION_PLAN.md`.
2. **Bridge between different Schatten notions — conditional progress, unconditional identification open.** Real projective nuclear infimum for the heat/resolvent and complex Physlib/CFC `TraceClass` are different implementations. `UltrasphericalSturmLiouvilleRealHeatComplexCFCS1Bridge.lean` now provides a *conditional* sharp identity when a positive complex operator has a full eigenbasis with the same heat spectral multipliers (or an explicit intertwiner). This does **not** identify an arbitrary chosen complex CFC Gram with the real heat operator or prove that the matching-spectrum/intertwiner hypotheses hold for it. Independently audit the conditional bridge's exact CI and prove those hypotheses for a concrete operator before transferring norms.
3. **Closed spheroidal commutation.** The pointwise exponential kernel balance does not establish that the integral Gram operator preserves the canonical unbounded spheroidal domain or commutes with its selfadjoint realization. Domain invariance and weighted Green/endpoint arguments must be certified independently.
4. **Exact paper-to-kernel crosswalk.** Compare each printed proposition/theorem (including normalization, Fock adjoint, all Schatten exponents, Funk–Hecke, Catalan/Bessel specialization and rational remainder) with current Lean statements and their exact successful CI; labels and hypotheses differ across older manuscript and newer source snapshots.
5. **Update the manuscript's certification claims.** The accessible `V007.2.tex` dates from 31 October and predates much of the November certification work. Its §9 ledger cannot be treated as current without a separately reviewed manuscript revision.

## Next actions

- Address the general real compact-operator singular decomposition, without assuming a complete target basis or equality of kernel/cokernel defects; reuse the certified two-incomplete-family nuclear theorem as the final *conditional* step.
- Independently audit the three Section 4 Lean bridge modules (analytic Fock realization, imaginary-segment adjoint, exact Gram/Kummer trace) against the text of `V007.2.tex`. Record theorem signatures and per-module CI logs.
- Certify (or explicitly mark outside scope) the §6 closed spheroidal commutation/domain-invariance claim; keep it separate from the already formalized pointwise identity.
- Prepare a subsequent editorial revision of the V007 manuscript with current theorem evidence, without editing V097 or V170.

**Non-action:** this is an audit document, not a claim that all ~834 changed Lean modules of PR #16 or every claim in V007.2 have received a complete independent axiom audit. The prior manuscripts V001/V097/V173, main branch, and V170 workflows remain untouched.
