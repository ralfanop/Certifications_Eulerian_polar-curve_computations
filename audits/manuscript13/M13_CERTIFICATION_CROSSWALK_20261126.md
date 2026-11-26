# Manuscript 13 — certification crosswalk, 26 November 2026

Source checked against the author-supplied **Manuscript_13_20261126_REMARK48_CUT.pdf**, 42 pages, 132 numbered equations. This is a status ledger, not a claim of exhaustive Lean correspondence. It supersedes the numbering references in the 25 November cross-connection PRs; the historical PDFs and source files remain unmodified. Section 11 of the 25 November draft was moved to §4.4 as Proposition 4.13.

## Exact numbering and scope

| Current source | Earlier source | Lean modules / PRs | Certified scope and limitations |
|---|---|---|---|
| §4.3, local magnetic and gauge identities (before Prop. 4.9) | same | #552 (M13/M16) | Integrated local identities; not a complete manifold-operator construction |
| Prop. 4.9, p.20, (60)–(63) | same | #572 GlobalHolonomy20261124 | Abstract path transport criterion, charged phases and domain equivalence; smooth line integral, smooth phase and unbounded selfadjoint domains remain |
| Prop. 4.11, pp.21–22, (64)–(73) | same | #557 radial derivatives; #558 EllisFourier20261124; #571 EulerianPositiveDefinite20261124 | Actual radial identities, Cauchy mass, derivative domination, zero-frequency mass, cosine averaging and conditional Fubini, real Gram positivity; full Fourier transform, complex PD and geometric/differential operator identification not claimed |
| Cor. 4.12, pp.22–23, (74) | same | #558, #570 BirmanOperator20261124, #582 EllisGramKernelOperator20261124 | Actual causal rows in real L², bounded linear integral operator A and nonnegative AA*, exact row norm and integrated diagonal mass; not yet the complex weighted free differential resolvent |
| Cor. 4.12, (75), (77) | same | #558, #570, #582; #633 EllisParsevalTonelli20261126 | Kernel energy π/(4aκ) proved; abstract diagonal-summability bridge; #633 attempts discharge by actual Parseval/Tonelli, pending audit |
| Cor. 4.12, (76) | same | #558 EllisBirman20261124 | Conditional spectral-series inequalities; ordinary Fredholm determinant of concrete weighted differential resolvent is not yet certified |
| Prop. 4.13, p.23, (78)–(79) | Prop. 11.1, (127)–(128) | #615 CrossThroatElliptic20261125 | Actual normalized quarter-power integral, scale and tangent substitutions, integrability, b'K(b) identity |
| Prop. 4.13, (80) | (129) | #615 | K(b)-to-Z(b) identity used as named hypothesis; actual definition of M12 Z(b) and derivation from its source still required |
| Prop. 4.13, (81) | (130), augmented AGM/Gamma expressions | #615, M12 #508, #634 CrossThroatLemniscate20261126; Arb #617 | Exact imported critical quartic Gamma integral, conditional self-dual normalization; #634 attempts actual lemniscate/Beta evaluation, pending CI. Analytic AGM identity still a classical input. Independent numeric AGM/Gamma enclosures certified |
| Remark 4.14 | Remark 4.13 | — | Interpretive distinction, no separate theorem claimed |
| Theorem 4.15, pp.24–25, (82)–(85) | Theorem 4.14, (78)–(81) | #568 MellinRindler20261124, #575 MellinL2LogJacobian20261124, #581 MellinPlancherelMultiplier20261124 | Logarithmic unitary equivalence and Fourier–Plancherel, actual band multiplier and sharp norm, idempotent spectral projection, cosine integral; differential-generator closure and full complex convolution kernel not yet identified |
| §5 onward, (86)–(132) | equations shifted by four until the former §11; former §12/13 now §11/12 | legacy record at f79d60f3 | Existing certification record must be audited theorem by theorem before declaring complete coverage; not re-certified by this additive ledger |

## Verified exact-head runs and merges

| PR | exact HEAD | successful run | merge commit | audited declarations |
|---|---|---:|---|---:|
| #558 | d2c6140dc64110efe9f6c71a49613dbd05f6c27f | 45400278078 | b1b23174d487b0282d13d9c0c57ac6f3d2b5447b | 21 |
| #568 | 3777afcd12e7f94500676d9f9eb887dba5420e08 | 45379453843 | fa68116420b261a698a636bcb83433e8478d815d | 14 |
| #570 | b08fc3f698759e9a49bec891e5a5252b60a1ccb4 | 45400288925 | 28e6da26f934c1cbf9ae121b81bd95da71aea63d | 10 |
| #571 | 7f8f52858b43e8d11a0e8f3a8cf573f69e783b44 | 45389157237 | 128d76a16b7c08ed6746db03ec7426e0195a11a6 | 8 |
| #572 | 534a6ca649a9e630b0b08285db9d054e9c0a2703 | 45389163482 | 5bfec5b5cb779f4e92688bd1ed9c518414770866 | 14 |
| #575 | 6fd316d3bd2e9fa92e9a37f0c59bb24af9b5155d | 45400268810 | 3221ad1a4f2d475ed7f3a2375127fe791cbeb493 | 20 |
| #581 | 6dc0f4690c641032ed58a150c057186ab55fa06f | 45776639809 | 49342a1016c6220b99f833ece9d24dc44fa5d6b2 | 27 |
| #615 | 89325d79d8aec7043b6e66af197c6543b5b8274e | 45776631190 | 3db0c55a5103b7d5f02ace98b3347144c6dc52a1 | 26 |
| #582 | 5ef4437604fb834709a88f2a2b96d39c18f0cbd7 | 45831557530 | 7e63b6c195e9c20dd737193f110ff98241da02a9 | 22 |

Total **162 audited declarations** in these nine additive modules/PRs, including definitions and conditional theorems, not 162 independent manuscript theorems. Standard axiom allowlist propext, Classical.choice, Quot.sound. #552 and #557 also merged, excluded from this subtotal. #633 (12) and #634 (19) are candidates, excluded until exact-HEAD kernel and axiom success. #633 first run 45831943333 failed; correction head 6244a0e38fdf9cc1f5d64632f098317a3c4df603. #634 head b709a3719701ad50e3c2147fb7c71626ae38eb71.

## Arb

* #554: strict fixed 30,000-place replay of earlier M13–M16 balls, merged 5effac4589338f9c6fa80c301d19ca2afd9e176f. Not counted in additive totals.
* #583: nine distinct benchmark quantities for (68)–(70), (75)–(77), and (84), including exp(π/(4aκ)) as an upper bound, **not** the Fredholm determinant. Run 45407631292, exact head 43f4134340347f4ea2a89a5a5df917a955dd459d, merge d5b3bc0f0432b4a767e46542c10d478112072c7b; minimum relative bits 3,599,996.
* #617: two independent enclosures for one scalar (81), the lemniscate constant A, AGM and Gamma. Run 45596018816, exact head 6d1b646ce559334aae92262d24d85a8196e70bbb, merge 29509d068f1798fac6a5bff3f21b5d73a8ecbf73; minimum relative bits 3,599,994. Both CI rounding and manifest gates succeeded.
* Both use 3,600,000 working bits, strict 1,000,001 significant-digit rounding and 30,000 fixed decimal places. Eleven evaluations of ten distinct scalars. Numerical interval agreement does not establish analytic identities.

## Outstanding tasks

1. #633: prove the actual Hilbert-basis energy/diagonal summability; certify on corrected HEAD.
2. Identify the complex differential resolvent and multiplication by sqrt(Va); prove positivity, selfadjoint domain, trace class and genuine Fredholm product (74)–(77).
3. #634: prove the self-dual overlap via the real lemniscate/Beta integral; validate. Independently prove the AGM formula or classify explicitly as a classical cited theorem. Obtain actual M12 pp.70 eqs.(357),(358) and certify the general Z identity, without defining Z by the desired result.
4. Audit the remaining original M13 statements individually, including manifold phase and dilation-generator closure.

## Code Availability replacement (proposed, not a manuscript edit)

The Lean 4 and Arb sources are available in the repository https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations. The earlier certification record Manuscript13_Certification.pdf (commit f79d60f3) is supplemented by the updated equation-to-certificate crosswalk, audits/manuscript13/M13_CERTIFICATION_CROSSWALK_20261126.md. The crosswalk identifies exact commits, successful CI runs, certified results and outstanding analytic dependencies. For the revised §4.4, the actual normalized overlap and its elliptic-period reduction have been formalized; the independent AGM and Gamma interval certificates for (81) agree at 1,000,001 significant digits. The full differential-resolvent, trace-class and Fredholm-determinant identification, and the general binary-quartic normalization, remain distinct formalization obligations.
