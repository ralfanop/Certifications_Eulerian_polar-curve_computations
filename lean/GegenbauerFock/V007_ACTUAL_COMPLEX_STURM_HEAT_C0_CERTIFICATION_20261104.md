# V007 — The genuine complex Gegenbauer Sturm C₀ heat semigroup

**Status as at 4 November 2026: kernel-certified for the actual complex C₀-semigroup.**
Repository: [ralfanop/Certifications_Eulerian_polar-curve_computations](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations).
Branch: `gegenbauer-fock-formalization-20261025`.
PR: [#16](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/16), **draft; no merge**.
Toolchain: the pinned Lean 4 / Mathlib versions in the repository.

## Mathematical construction

For `lambda>0`, write

```text
HR = L²(nu_lambda; R)
HC = L²(nu_lambda; C)
```

and let `H_s: HR ->L[R] HR` be the actual strongly continuous Gegenbauer Sturm heat semigroup, whose generator was previously identified with the graph closure of the genuine polynomial Sturm operator.

The maps

```text
J  : HR ->L[R] HC              (real-valued L² inclusion)
Re : HC ->L[R] HR
Im : HC ->L[R] HR
```

are concrete bounded maps constructed using Mathlib's pointwise Lp composition `ContinuousLinearMap.compLpL` on the actual weighted L². They satisfy, on the ENTIRE spaces,

```text
Re(J f) = f,
Im(J f) = 0,
J(Re z) + I • J(Im z) = z,
||J f||_HC = ||f||_HR, J injective.
```

The complex semigroup is defined explicitly by its actual complex-valued L² action:

```text
H_s^C z = J(H_s(Re z)) + I • J(H_s(Im z)).
```

The real-linear extension is shown to commute with multiplication by `I`, and thereby is promoted to a BOUNDED COMPLEX-linear operator `sturmActualComplexHeatCLM lam hlam s hs : HC ->L[C] HC`. It is NOT an auxiliary diagonal model and is NOT the unrelated Fock Gram.

## Kernel-verified components and audit

| Result | CI | Outcome |
|---|---|---|
| Exact real/imaginary L² decomposition | [#41823421954](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41823421954) | SUCCESS; 9,191 jobs |
| Real-linear actual-complex-L² heat and intertwining on embedded real vectors | [#41823422148](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41823422148) | SUCCESS; 9,192 jobs |
| True COMPLEX-linear heat and exact `H_s^C J=J H_s` | [#41824600170](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41824600170) | SUCCESS; 9,193 jobs |
| Isometric and injective actual real-to-complex inclusion | [#41825094792](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41825094792) | SUCCESS; 9,192 jobs |
| Exact complex operator identity at time zero and additive semigroup law | [#41838327220](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41838327220) | SUCCESS; 9,196 jobs |
| Strong right continuity at zero on EVERY complex L² vector; combined C₀ certificate | [#41838689703](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41838689703) | **SUCCESS; 9,200 jobs** |

All verified theorem axiom prints use only `propext`, `Classical.choice`, `Quot.sound`, with **no** `sorryAx` nor `Lean.ofReduceBool`.

## Certified final full C₀ statement

The Lean theorem

```text
GegenbauerFock.Ultraspherical.sturmActualComplexHeat_fullC0_joint_certificate
```

certifies, simultaneously,

```text
H_0^C = identity on HC,
H_(s+t)^C = H_s^C H_t^C for all s,t >= 0,
Tendsto (fun s => H_(max 0 s)^C z)
        (nhdsWithin 0 [0,+infinity)) (nhds z)
        for EVERY z in HC.
```

The actual isometric inclusion obeys `H_s^C (J f)=J(H_s f)` on the entire real L²; this last intertwining theorem is independently compiled in CI #41824600170.

## Direct Lean sources

- [Actual L² real/imaginary decomposition](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexLpDecomposition.lean)
- [Actual L² isometric inclusion](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexLpIsometry.lean)
- [Actual bounded real-linear heat extension](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexHeatRealExtension.lean)
- [Actual bounded COMPLEX-linear heat](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexHeatCLM.lean)
- [Complex heat zero and composition laws](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexHeatSemigroupLaw.lean)
- [Complex full C₀ theorem](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexHeatFullC0.lean)

## Explicit limitations / next research obligations

1. The new **complex C₀-semigroup** is fully certified. The present final combined theorem does **not** assert a separately formalized SHARP complex contraction norm `||H_s^C||<=1`, although the original real semigroup is contractive. A complex norm identity or an equivalent route must be certified before claiming sharp complex contractivity.
2. The exact identification of the complex infinitesimal generator with the appropriate **closed complexification of the genuine Sturm differential operator**, including its complete domain, still requires a separate graph-level certificate. Do not automatically transfer the already verified real generator identity.
3. For `s>0`, compactness and complex CFC trace class may be provable from the embedded eigenmodes after separately verifying their COMPLEX Hilbert-basis orthonormality and completeness. Do not equate an embedded real Hilbert basis automatically with a complete complex one.
4. Neither this operator nor its spectrum is identified with the **distinct** Gegenbauer--Fock Gram `C_(lambda,alpha)^* C_(lambda,alpha)`. The previous Lean-certified trace-gap obstruction excludes a basis-preserving intertwiner for `lambda=1/2`, `alpha=1`, every `0<s<=1/10`. That obstruction and this canonical complexification are mathematically compatible.
5. No merge to `main`; no changes to V097.

## Manuscript-ready theorem

**Theorem (Canonical complexification of the Gegenbauer Sturm heat semigroup).** For `lambda>0`, let `H_s` be the genuine Gegenbauer Sturm `C₀` heat semigroup on `L²(nu_lambda;R)`. On `L²(nu_lambda;C)` define

```text
H_s^C (u+i v) := H_s u + i H_s v
```

using the canonical actual-L² real-to-complex inclusion and real/imaginary part maps. This defines bounded complex-linear operators satisfying `H_0^C=I`, `H_(s+t)^C=H_s^C H_t^C` for all nonnegative times, and `||H_s^C f-f||_2 -> 0` as `s↓0` for every complex L² vector. The inclusion of the real weighted L² is isometric and intertwines `H_s` with `H_s^C`. The full `C₀` theorem, its precursors, and its axiom audit are verified in the CI runs above.


## 4 November 2026 — additional kernel-certified consequences

### Embedded actual-complex eigenmodes

The new module [`UltrasphericalSturmLiouvilleActualComplexHeatEmbeddedEigenmodes.lean`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexHeatEmbeddedEigenmodes.lean) was independently verified by [CI #41839176206](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41839176206): **SUCCESS, 9,195 compiled jobs**; all three theorem audits list only `propext`, `Classical.choice`, `Quot.sound`.

For each real normalized Gegenbauer basis vector `e_n`, its actual complex image `J(e_n)` is nonzero with norm exactly one and

```text
H_s^C (J(e_n)) = (exp(-s*n*(n+2*lambda)) : C) • J(e_n),
lambda>0, s>=0.
```

The formal theorems are `sturmActualComplexHeatCLM_normalized_Gegenbauer_eigen`, `sturmActualComplexNormalizedGegenbauer_norm_eq_one`, and `sturmActualComplexNormalizedGegenbauer_ne_zero`. **No complex-Hilbert-basis completeness is inferred from these three statements alone.**

### Full complex right-continuity at every nonnegative time

The new module [`UltrasphericalSturmLiouvilleActualComplexHeatRightContinuity.lean`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/gegenbauer-fock-formalization-20261025/lean/GegenbauerFock/UltrasphericalSturmLiouvilleActualComplexHeatRightContinuity.lean) was verified by [CI #41840061365](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41840061365): **SUCCESS, 9,201 compiled jobs**, only standard kernel axioms.

For every `lambda>0`, `t>=0`, and `f` in the ACTUAL complex weighted L²,

```text
H_(t+h)^C f -> H_t^C f as h decreases to zero through h>=0.
```

The theorem is `sturmActualComplexHeatCLM_tendsto_at_nonnegative_time_right`. It follows from the exact semigroup law and strong C₀ continuity, with no Gram identification.

### Remaining next-step obligations

The generator on the embedded canonical closed real Sturm domain is formalized in the separate new module `UltrasphericalSturmLiouvilleActualComplexHeatGeneratorRealCore.lean`, but its **CI must be checked** before reporting that result as certified. Full complex generator domain equality, sharp complex contraction norm, and full complex Hilbert-basis completeness remain independent goals.
