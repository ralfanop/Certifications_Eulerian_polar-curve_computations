# M16 v16.6 — frozen §13 identity reconciliation (2026-11-18)

## Authority and reproducibility

The author's newly supplied `Manuscript_16_AI_Declaration_20261118(1).zip`, Library ID `libfile_7d165801f840819198fb80548adc639d`, SHA-256 `1f316919eae73c3459fdbdf0572ba1d523aca297cd18594faae0efd6655895d4`, is revision 16.6 (title-page date 17 November). Compared directly against the previously approved v16.5 ZIP `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`. No alternative manuscript sources used.

| Extract of 16.tex (inclusive line ranges) | v16.5 | v16.6 |
|---|---|---|
| §§2–13 | 173–1880: 7f7585aef3a1c9a7b8a3d670474cae67ecd026c377ef544f64232bd472f7f759 | 178–1885: 9b65b0e36c5a1800061e646fe4eed591d57486c3dd0f15e052a762075b763024 |
| **§13** | 1658–1880 | 1663–1885 |
| §13 SHA-256 | 21fec377ce89f5ffd47c13b1f8d38a5e3453965c578e1d937d16bd5bfd2a1bdd | 21fec377ce89f5ffd47c13b1f8d38a5e3453965c578e1d937d16bd5bfd2a1bdd |
| Original §14 prefix | 1881–2055 | 1886–2060 |
| Original §14 SHA-256 | f68d11222d3c926bf708e980773d1c5b8f6950f7e37ee24a8e3caaabbe8e3a73 | same |
| Full §14 | original | 1886–2212: 996bf1dc7c6f49ea753710d15df162bc6a8000be8bdce395c73fb7cacaad5c61 |

Reproduce: `unzip -p "$archive" 16.tex | sed -n '1663,1885p' | sha256sum` for the new archive; use 1658–1880 for the old. Diff of the two §13 streams is empty. §§2–13 as a whole are NOT byte-identical: the only two differing paragraphs are in the remarks [Comparison with the four-dimensional charged-fermion example] and [Inter-boundary couplings and quantum correlation], with references removed and scope shortened; no changed equation or hypothesis there. The old §14 prefix is also byte-identical. v16.6 adds §§14.4–14.5 (Theorem 14.6, Corollary 14.7, Theorem 14.8, Corollary 14.9), not part of this §13 audit.

## A. Exact mapping of historic scalar certificates

The two reference operators must never be interchanged: §9 uses the spatial `mathscr L_0 = Delta_T ⊕ D_3`; §13 uses the mixed nonresonant periodic wave and spatial Dirac `L_0 = W_R ⊕ D_3`. The label `eq:fourthtrace` belongs **only** to the former. Its closed scalar expression is not the mixed fourth trace. In particular, no new closed mixed trace is printed in the frozen §13; #306 is a supplemental derivation. Both use the same spatial Dirac multiplicity **per sign**, and the Dirac fourth trace counts both signs.

| Certificate / exact source | Exact closed scalar expression | 12 decimal places | Relative bits (strict million-digit replay) |
|---|---|---:|---:|
| #301 → #396 `eq:ktrace2` (spatial transverse K) | 2(ζ(2)−ζ(4)) | 1.125221666274 | 3599994 |
| #301 → #396 `eq:diracfourthzeta` | π²−π⁴/12 | 1.752180148256 | 3599993 |
| #301 → #396 Maxwell spatial component of `eq:fourthtrace` | 2(ζ(6)−ζ(8)) | 0.026531411573 | 3599988 |
| #301 → #396 `eq:fourthtrace` | π²−π⁴/12+2(ζ(6)−ζ(8)) | 1.778711559829 | 3599992 |
| #306 → #318 mixed periodic W_R, ζ form | (4ζ(2)ζ(4)−2ζ(4)²+ζ(8))/128 | 0.045176809575 | 3599994 |
| #306 → #318 mixed periodic W_R, π form | π⁶/17280−π⁸/907200 | 0.045176809575 | 3599995 |
| #306 → #318 mixed L_0 **E=0** | π²−π⁴/12+π⁶/17280−π⁸/907200 | 1.797356957831 | 3599993 |

Numerical evidence re-inspected in the actual logs: #318 run 43701995391 job 132774933894 (3 checks, all exact cell PASS); #396 run 44322620584 job 134865294007 (4 historical spatial checks among 14, all exact cell PASS). Both used python-flint 0.9.0, working precision 3600000 bits, asserted >=3400000 relative bits on each nonzero entry, and strict exact endpoint tests at 1000001 significant digits. Scripts `numerics/arb/million_decimal_m16.py` and `numerics/arb/m16_v165_reconciliation_million.py` call `million_decimal_common.py`; reproducible rounded digits and rigorous balls are retained in the original artifacts. #396 also has an exact rational endpoint stream. The two forms of the periodic-wave expression are the same mathematical quantity, not two independent constants. No new numeric run needed for an unchanged identity, no old artifact overwritten. These are rigorous **closed-expression enclosures**, not operator trace identification. Neither trace formula gives the fourth trace for arbitrary E≠0 or for K=B L⁻¹ C.

## B. Supplemental exact mixed fourth-sum reconciliation

From frozen `eq:mixed-maxwell-index-164` and d_ell=2(ell²−1), the nonnegative scalar sum is

```
S_W = sum_{ell>=2} 2(ell²−1) sum_{k∈Z, k≠0,-ell} (4|k||ell+k|)^(-4).
```

Partition k>0, k<−ell, and −ell<k<0. Set (a,b)=(|k|,|ell+k|). The interior gives all ordered positive pairs a+b=ell; the exterior two ranges give all ordered positive pairs |a−b|=ell. There are no duplicate pairs within each branch. Both series converge by the §13 p=4 estimate: at most four modes at each positive minimum j, yielding C sum ell^(-2) sum j^(-4). Nonnegative rearrangement is therefore legitimate. Then

```
128 S_W = sum_{a,b>=1} ((a+b)²−1)/(a⁴b⁴)
        + sum_{a,b>=1, |a−b|>=2} ((a−b)²−1)/(a⁴b⁴).
```

The difference-one terms vanish. Extending the second sum to all positive pairs introduces the negative diagonal −ζ(8), which must be corrected by **+ζ(8)**. After this extension all signed pieces are absolutely summable (bounded by combinations of ζ(2)ζ(4) and ζ(4)²). The sum of the two numerators is exactly 2(a²+b²−1). Products of convergent positive p-series therefore give 128 S_W = 4ζ(2)ζ(4)−2ζ(4)²+ζ(8). Substitution of even-zeta values gives the π form. This reproduces #306 without changing it. #306's actual Lean audit only covers the five arithmetic declarations, not infinite reindexing, zeta products, or spectral realization. Written derivation above is not a Lean proof.

## C. Frozen §13 equation-by-equation certification boundary

Labels are authoritative; all 17 display equations are 124–140 in order before §14. No physical interpretation is inferred. The exact rationals 1/4, 2/3, 3/2 are symbolic, not assigned fictitious relative bit accuracy.

| Frozen source label (prefix eq:) | Identity / obligation | Verified scope and remaining gap |
|---|---|---|
| mixed-spaces-164 | P, R, X=R⊕L²(S³;Σ), H_RD=P⊕X | Abstract typed spaces #366; concrete orthogonal decompositions and bundle realizations open. |
| mixed-L0-164 | L₀=W_R⊕D₃, maximal-domain direct sum | Reference graph equivalence is input of #401; concrete spectral graph space open. |
| mixed-L0gap-164 | max(1/4,2/3)=2/3 | Exact scalar; concrete inverse norm equality needs spectral realization and extremizers. #401 assumes ≤2/3 in ambient norm. |
| mixed-schatten-164 | L₀⁻¹∈S_p iff p>3 | #305, #310, #321, #331–333, #336, #368 address comparisons, finite shells, actual p=3 nearest-mode nonsummability. #344 written audit. Operator iff and perturbative ideal stability open. |
| mixed-inverse-bound-164 | ‖L⁻¹‖≤1/(3/2−‖E‖) | #322 scalar; #401 actual ambient operator bound under reference equivalence and norm hypothesis. |
| mixed-maxwell-index-164 | |ell²−m²|=4|k||ell+k| | #306 arithmetic; exact frozen domain m=ell+2k, k≠0,−ell. |
| mixed-upper-series-164 | ≤4/(2ell)^p × sum j^(−p), p>1 | #306 nearest-mode inequality; #332–336 finite card ≤4; full infinite upper estimate for actual integer-index series remains open. |
| mixed-lower-series-164 | sum 2(ell²−1)/(4(ell+1))^p | #310/#321 finite p=3 comparison, #368 genuine p=3 nonsummability. General p≤3 and spectral-operator transfer open. |
| mixed-Linverse-164 | L⁻¹=L₀⁻¹(I+EL₀⁻¹)⁻¹ | #401 checked typed construction and inverse formula; embedding j explicit. Compact/Schatten iff transfer still open. |
| mixed-A-164 | A:P⊕D→P⊕X | #366 actual continuous linear map; B in Lean is B_ambient∘j when specialized. |
| mixed-F-164 | F=A_P−B L⁻¹ C | #366 actual typed Schur map; compactness of correction open. |
| mixed-index-164 | ind A=ind A_P when Fredholm | #397/#400 prove ind A=ind F and Fredholm equivalence; Atkinson stability F=A_P−K open. |
| mixed-gap-164 | |μ|>‖B‖‖C‖/(3/2−‖E‖) | Reference inverse bound #401; second Neumann proof on resonant space with ambient B,C norm estimate open. |
| mixed-factor-164 | triangular graph-domain factorization | #366 actual equality; #374 kernel; #397 range and bijectivity; #400 cokernel/index. All conditional on L graph equivalence, now constructible under #401 hypotheses. |
| mixed-neumann-164 | F=μ(I−μ⁻¹K) and norm <1 | exact scalar gap, operator implementation and coupling specialization still open. |
| mixed-det4-164 | Δ₄(μ)=det₄(I−μ⁻¹K), μ≠0 | #395/#398/#402 shared diagonal det4 model is not this potentially nonnormal K; actual S₄ ideal and regularised determinant construction open. |
| mixed-det4-criterion-164 | A invertible iff Δ₄(μ)≠0 | #397 block bijectivity reduction; actual determinant zero criterion, eigenvalue multiplicities and discreteness open. |

The source's three named results are not certified in their entirety. Careful distinction: no operator on the periodic *spacetime* Dirac spectrum was identified with D₃; no perturbed fourth-trace formula is presumed; no physics or photon-mass identification.

## D. Exact HEAD workflow snapshots (2026-11-18)

The table is an independent query of PR HEAD and PR-triggered workflow results, not a guess from merged status. #344 and #345 returned no workflow, hence written/candidate only. #330 later gained a scalar estimate check, not full graph theory. #401 audit was inspected after fixing its previous failure; #400 and #397 were independently inspected on their exact heads. All three verified axiom lists contained only propext, Classical.choice, Quot.sound. #306 actual Lean log same whitelist (subsets); numeric evidence above. Other historic CI statuses do not broaden their proof scope.

| PR | Exact HEAD | Workflow result |
|---|---|---|
| #301 | `673bf7453dbfd7ce0eed7b12fe52c03e6f8185df` | [43631045048](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43631045048) SUCCESS; [43631045041](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43631045041) SUCCESS |
| #302 | `5b203bf95720f7807abc3bd0e37848f27bc246fe` | [43632779419](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43632779419) SUCCESS |
| #303 | `1ec8c687f8273970f64fc37320e266a054dc03de` | [43636464042](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43636464042) SUCCESS |
| #305 | `18fa2ae389892ff4d05019852c45c3862d07d54c` | [43642321143](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43642321143) SUCCESS |
| #306 | `d761faf648d4501603317cda60b9ef603a4c275c` | [43643396223](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43643396223) SUCCESS |
| #310 | `2b55a144940bc540d84d06bf8e6a83af90707d40` | [43697054703](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43697054703) SUCCESS |
| #318 | `cbdef6bc71522d4a49186fcb07a13c01df31a513` | [43701995391](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43701995391) SUCCESS |
| #321 | `440ae3df80363d04066e483488d1a355ffa295ed` | [43708522272](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43708522272) SUCCESS |
| #322 | `3a41913f984fd48fd6933b46e5cd0f6737095958` | [43720497284](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43720497284) SUCCESS |
| #324 | `c7f770618a4150be3f927295f94a6357b28b04e3` | [43720546203](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43720546203) SUCCESS |
| #326 | `be0f8d4c76599f7025f4afc035dc0655dd8b57e8` | [43732983351](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43732983351) SUCCESS |
| #330 | `40634b1c77136c8f7dce00266c4d64f5b08a4454` | [43772118144](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43772118144) SUCCESS |
| #331 | `3ccdde9e2f70b9fdd912e09597791818b7d0507d` | [43813762175](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43813762175) SUCCESS |
| #332 | `8a23eb4b5cd32fc7247dc202412bb6c31f7594be` | [43853207123](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43853207123) SUCCESS |
| #333 | `5d21a94f8169e6e1875e3e46d7e029c25d7e2ee7` | [43901218498](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43901218498) SUCCESS |
| #336 | `8d66c057317c49ed88992b014e66b992294445fe` | [43938118638](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43938118638) SUCCESS |
| #344 | `f1da24f3fb90aaf5536fcfae56b0cb81bd2dbfb6` | No PR workflow returned; not a kernel certificate |
| #345 | `345b057eba4bfd1371f378b5806b30b2b45f9857` | No PR workflow returned; not a kernel certificate |
| #366 | `16768dd9d12b8a4edb5e8ed0a70a1ce20ce0907a` | [44186046488](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44186046488) SUCCESS |
| #368 | `a2929ab87a64978d97dc2680b5b0e6a570e6c61f` | [44186367036](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44186367036) SUCCESS |
| #374 | `c9dcf753d9dac9285fd4e0fdbabc156a39c2c0bb` | [44222952381](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44222952381) SUCCESS |
| #396 | `a0398cd99b0bf9b5e4077785b0b5748dde6f3827` | [44322620584](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44322620584) SUCCESS |
| #397 | `cac0d4e1cdb4946f27b18ecc3f2540c37bf063c0` | [44322847801](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44322847801) SUCCESS |
| #400 | `9f1d0e564ffb68e4374b7356a02d11cfd3cc212c` | [44323752948](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44323752948) SUCCESS |
| #401 | `903829959aad06fb03c7772c447b9a13f10e077a` | [44325350321](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44325350321) SUCCESS |

## E. Next work, after reconciliation

1. Concrete graph-domain and spectral realization of reference L₀, exact gap and two-sided Schatten criterion; actual infinite shell sums and mixed fourth reindexing in Lean.
2. Prove compactness of ambient inverse transfer and of B L⁻¹ C, then second Neumann sufficient resonant gap. Distinguish any compactness theorem from full Atkinson/index stability.
3. Actual compact perturbation invariance and Fredholm index zero in the scalar-shift case.
4. General operator S₄ and regularised determinant criterion for K, including multiplicities; shared diagonal product is only a specially structured model.
5. Continue separately with §14 original and newly added v16.6 obligations, avoiding duplication of #346 and later work.

This is a source reconciliation ledger, not a new Lean or Arb certification. No manuscript or prior certificate modified; no merge by this agent.
