# V007 — Real Schatten S₁: what is kernel-certified, and the remaining partial-isometry gap

Date: 3 November 2026. Branch: `gegenbauer-fock-formalization-20261025`, PR #16 remains Draft/unmerged.

## Verified kernel-certified foundations

1. **Actual closed real Sturm resolvent:** `UltrasphericalSturmLiouvilleResolventRealNuclearDualLower.lean`; [CI #41500000883](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41500000883) SUCCESS, 9108 jobs; the real nuclear projective infimum over **all** admissible rank-one representations equals the positive Gegenbauer spectral trace.
2. **Genuine positive real spectral-S₁ bridge:** `UltrasphericalSturmLiouvilleResolventRealS1SpectralBridge.lean`; [CI #41717693474](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41717693474) SUCCESS, 9111 jobs.
3. **General positive operator with a countable complete Hilbert eigenbasis:** `UltrasphericalSturmLiouvilleResolventRealS1EigenbasisToNuclear.lean`; [CI #41718447315](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41718447315) SUCCESS, 9112 jobs, with sharp projective norm equal to the positive eigenvalue sum.
4. **General left-unitary invariance of nuclear cost sets and their infima:** `RealNuclearUnitaryLeftInvariance.lean`; [CI #41721636724](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41721636724) SUCCESS, 9113 jobs; holds for arbitrary real nuclear operators without positivity or normality.
5. **Actual real Sturm Hilbert–Schmidt mass independent of any chosen complete real basis:** `UltrasphericalSturmLiouvilleRealS2BasisIndependence.lean`; [CI #41721440858](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41721440858) SUCCESS, 9097 jobs.

All listed successful CI logs had explicit `#print axioms` checks with only `propext`, `Classical.choice`, `Quot.sound`. No unverified result is to be treated as certified.

## Further verified real nonselfadjoint S₁ certifications (3 November 2026)

6. **Two full real Hilbert singular bases imply a unitary-polar factorization and true nuclearity**: `RealNuclearUnitaryPolarS1Bridge.lean`; [CI #41722591697](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41722591697) SUCCESS, 9114 jobs, four clean-axiom theorems.
7. **Exact norm for the SPECIFIC supplied two complete singular bases**: `RealNuclearSingularS1ExactGivenBases.lean`; [CI #41723296935](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723296935) SUCCESS, 9115 jobs, three clean-axiom theorems.
8. **Nuclear cost-set and norm invariance under right and two-sided unitary multiplication**, with no selfadjointness assumption: `RealNuclearUnitaryRightTwoSidedInvariance.lean`; [CI #41723512868](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723512868) SUCCESS, 9114 jobs, six clean-axiom theorems.
9. **General nuclear projective norm dominates the operator norm, hence is nondegenerate on nuclear operators**: `RealNuclearInfimumDominatesOperatorNorm.lean`; [CI #41723806687](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41723806687) SUCCESS, 9106 jobs, four clean-axiom theorems.

These claims apply on their precisely stated domains; in particular, two full bases and a global unitary phase do not cover unequal kernel/cokernel defect dimensions.

## Still pending exact-SHA Lean certification

- `RealNuclearRankOneImpliesCompact.lean`, [CI #41724362531](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41724362531), attempts to prove that every real nuclear operator is compact, using rank-one factorization through the scalar field and norm-closedness of compact operators. Do not cite the theorem as certified until a successful job and clean kernel axiom audit.

## Important mathematical gap: an arbitrary nuclear operator need NOT have a global unitary phase

A two-sided SVD of the form `T(b_n)=sigma_n c_n`, with *both* `b` and `c` complete Hilbert bases indexed by the same countable set, imposes an extra defect compatibility condition. A nonzero nuclear operator can have unequal kernel and cokernel dimensions. For instance, on real `ℓ²(ℕ)`, let

\[
T e_n = 2^{-(n+1)}e_{n+1}.
\]

This positive-weight unilateral shift is compact and nuclear, is injective, and has range closure of codimension one. Its source singular vectors form the standard complete basis, but the obvious positive singular **output** vectors `e_{n+1}` miss `e_0`. Its polar phase is a proper isometry, not a unitary. Consequently the sufficient two-complete-basis/universal-unitary criterion does **not** by itself prove general equivalence for every real Schatten-S₁ operator.

A full real Schatten theory must use a **partial isometry** `W` on the support of `|T| = sqrt(T* T)`, while allowing distinct source/output defect subspaces. In particular, avoid inferring a global unitary from an arbitrary compact real operator.

## Exact remaining kernel-level milestones

1. Nuclear-series membership implies compactness of `T`, using compactness of each real rank-one term, stability under finite sums, and closedness of compact operators in operator norm.
2. Construct the genuine real CFC positive square root `|T| = (T* T)^{1/2}` for arbitrary compact `T`; establish the correct support and kernel statements and its relation to singular values.
3. Obtain a complete source eigenbasis (and a potentially incomplete output orthonormal singular family) for `|T|` by real compact selfadjoint spectral theory.
4. Prove a **two-orthonormal-family** finite nuclear trace dual bound, with coefficient one, for `sum_{n<N} inner(v_n, T(b_n))`, using Bessel/Cauchy–Schwarz on both sides; no complete output basis or unitary phase is assumed.
5. Pass to arbitrary absolutely summable rank-one series and to the infimum. For every actual real compact operator satisfying `∑ sigma_n<∞`, prove `||T||_N = ∑ sigma_n` and conversely show nuclearity forces that sum to converge.
6. Establish trace-norm triangle, homogeneity, completeness, and sharp two-sided bounded-operator ideal inequalities for the nuclear class, then connect to an independently defined real singular-value/CFC norm rather than the existing complex `ProbabilisticTheory.IsTraceClass` by an unjustified coercion.
7. Expand proofs to finite-dimensional and non-countable Hilbert-basis settings separately, or state countable-separable hypotheses explicitly.

No modifications to `main`, V097, V170, toolchain, or Mathlib lock are authorised by this plan.
