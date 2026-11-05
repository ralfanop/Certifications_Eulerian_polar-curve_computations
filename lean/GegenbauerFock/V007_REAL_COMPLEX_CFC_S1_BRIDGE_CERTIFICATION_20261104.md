# V007 — Real-to-complex positive spectral S1 bridge: certified scope

**Date:** 4 November 2026  
**Repository:** `ralfanop/Certifications_Eulerian_polar-curve_computations`  
**PR:** [#16](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/16), branch `gegenbauer-fock-formalization-20261025` (draft; no merge).  
**Formal system:** pinned Lean 4 `v4.35.0-rc3`, repository-pinned Mathlib.

## 1. Kernel-verified new results

| Scope | CI | Result | Kernel axioms |
|---|---|---|---|
| Real-linear complete-eigenbasis intertwining transfers positive spectral data and equates real/complex S1 under explicit complex CFC class hypothesis | [#41806402158](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41806402158) | SUCCESS; 9,160 jobs | Standard: `propext`, `Classical.choice`, `Quot.sound` |
| Genuine complex CFC IsTraceClass membership **derived** from a positive summable diagonal; matching-real/complex-S1 and intertwining versions with no assumed complex class membership | [#41807980398](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41807980398) | SUCCESS; 9,161 jobs | Standard only |
| Specialization to the **actual** real Gegenbauer heat semigroup and a matched positive complex operator; CFC trace-class membership and exact S1 equality, both via matched eigenvalues and explicit intertwining | [#41807980319](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41807980319) | SUCCESS; 9,190 jobs | Standard only |

All three workflows build the named Lean module, execute a `#print axioms` audit and check that neither `sorryAx` nor `Lean.ofReduceBool` appears. The intermediate initial run [#41807482425](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41807482425) failed due to two reversed congruence directions; fixed in [`824e84af`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/824e84af5ea67173f8b2fda678296910fbe5dd2f), with the successful CIs above.

**Formal Lean modules**

- [`RealComplexPositiveSpectralIntertwining.lean`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/RealComplexPositiveSpectralIntertwining.lean)
- [`RealComplexPositiveSpectralAutomaticTraceClassBridge.lean`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/RealComplexPositiveSpectralAutomaticTraceClassBridge.lean)
- [`UltrasphericalSturmLiouvilleRealHeatComplexCFCS1Bridge.lean`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleRealHeatComplexCFCS1Bridge.lean)

## 2. Mathematical results and hypotheses

### Automatic CFC trace-class membership

Let `H_C` be a complete complex Hilbert space, `T : H_C ->L[C] H_C` a positive bounded operator, and `(b_n)` a complete complex orthonormal Hilbert basis. If

```text
SUM_n Re <b_n, T b_n> < infinity,
```

then Lean constructs a witness for `ProbabilisticTheory.IsTraceClass T`. This is the *source-compatible* Physlib CFC-absolute trace-class predicate, whose definition requires a SET-indexed Hilbert basis and summability of the diagonal of `CFC.abs T`.

Crucially, the proof is not a bare identification of different index types. It constructs `S=CFC.sqrt T`, uses `Re <x,T x>=||S x||²` and the kernel-certified basis-independence of the squared Hilbert–Schmidt norm, and thereby supplies a genuine set-indexed trace-class witness.

Lean: `complex_nonneg_isTraceClass_of_summable_natBasis_diagonal`.

### Automatic S1 norm equality for matched positive spectra

For a bounded operator `R` on a complete REAL Hilbert space and a positive bounded operator `T` on a complete COMPLEX Hilbert space, assume complete orthonormal eigenbases `(bR_n)`, `(bC_n)` and the SAME nonnegative summable real eigenvalues `sigma_n`:

```text
R bR_n = sigma_n bR_n,
T bC_n = (sigma_n : C) bC_n,
sigma_n >= 0,  SUM_n sigma_n < infinity.
```

Then Lean constructs `hTclass : ProbabilisticTheory.IsTraceClass T` and proves

```text
realNuclearInfimum R = ProbabilisticTheory.traceNorm T hTclass.
```

Thus complex CFC class membership is a conclusion, not an independent hypothesis. The *projective* real nuclear norm is the infimum over costs of all admissible real rank-one series; the complex norm uses the genuine CFC absolute-value predicate.

Lean: `realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_sharedSpectrum`.

### Real-linear intertwining version

Alternatively, the common complex spectral eigenvalue formula follows if there is a **specific** real-linear map `J : H_R ->[R] H_C` such that:

```text
J(bR_n) = bC_n    for every n,
T(J x) = J(R x)   for every real x.
```

These requirements, together with positivity of `T` and a nonnegative summable real spectrum, yield both its complex CFC trace-class membership and exact cross-field S1 norm equality.

Lean: `realProjectiveNuclear_eq_complexPhyslibTraceNorm_autoClass_of_intertwining`.

## 3. Specialization to the actual Gegenbauer heat semigroup

Let `lambda,s>0`. In the REAL weighted space `L²(nu_lambda;R)`, let `H_s` be the genuine closed-Sturm Gegenbauer heat semigroup element. The certified normalized Gegenbauer Hilbert basis `e_n` satisfies

```text
H_s e_n = exp(-s*n*(n+2*lambda)) e_n.
```

For any positive bounded COMPLEX Hilbert-space operator `T` possessing a complete Hilbert eigenbasis with **these same eigenvalues**, Lean constructs complex CFC trace-class membership and certifies

```text
realNuclearInfimum(H_s)
   = ProbabilisticTheory.traceNorm(T)
   = SUM_n exp(-s*n*(n+2*lambda)).
```

An alternative theorem uses a concrete `J` as above. The actual real heat operator `H_s` is not replaced by a formal diagonal surrogate.

Lean:

- `sturmRealHeat_actual_complete_eigenbasis`
- `sturmRealHeat_realS1_eq_complexCFC_autoClass_of_matching_spectrum`
- `sturmRealHeat_realS1_eq_complexCFC_autoClass_of_intertwining`

The independent exact real `S1` formula and graph/compact/nuclear joint certificate were already kernel-checked by [CI #41805555379](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41805555379).

## 4. Research limitations — do not overclaim

1. **NO concrete real-to-complex intertwiner J is constructed here.** Given `T` must satisfy matching eigenbasis and operator intertwining (or matching spectrum) as hypotheses.
2. **NO equality of spectra is asserted for the actual Gegenbauer–Fock Gram** `C_(lambda,alpha)^* C_(lambda,alpha)` and the heat operator `H_s`. The Gram's spectral multipliers are not assumed equal to `exp(-s*n*(n+2*lambda))`. A direct identification requires new, independent analytic and kernel-checked statements.
3. The complex predicate and norm are the **source-compatible PhyslibAlpha definitions selectively ported** into V007, not an assertion that the entirety of the upstream Physlib package has been imported or proved API-equivalent.
4. The theorem requires **complex operator positivity**; it has not been eliminated as an independent assumption by a general positivity-from-eigenbasis theorem.
5. Kernel certification establishes proof correctness under the listed hypotheses; it does not prove novelty or bibliographical priority.
6. Keep PR #16 draft; do not merge into `main` or manuscript V097.

## 5. Manuscript-safe formulation

**Proposition (Conditional real–complex positive spectral trace comparison).** Let `R` and `T` be bounded operators on complete real and complex Hilbert spaces, respectively, with `T >= 0`. Assume complete orthonormal eigenbases with the same nonnegative summable eigenvalue sequence. Then `T` belongs to the CFC-absolute trace class and its complex CFC trace norm equals the optimal projective real nuclear norm of `R`; both equal the spectral sum. In particular, this applies to the actual real ultraspherical heat semigroup at positive time whenever the selected positive complex operator has the same complete heat eigenvalue data (or an explicitly certified intertwining relation).

**Proof:** Lean 4 theorems and certified CI logs above. This is a *conditional* bridge, not a claimed correspondence between unrelated Sturm heat and Fock Gram spectra.
