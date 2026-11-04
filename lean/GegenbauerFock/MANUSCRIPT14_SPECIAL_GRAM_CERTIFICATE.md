# Manuscript 14.1 §6 — actual L² Gram specialization: kernel certificate

**Last verified CI:** [#41840633678](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41840633678), 4 November 2026, **SUCCESS** with Lean 4 and pinned Mathlib.  
**Source commit:** `5a1d466169450de888e9e25b17d16f22ad0d6eff`.  
**Base branch:** V007 `gegenbauer-fock-formalization-20261025`. New branch `manuscript14-v141-concrete-gram-v007-20261104`. **Draft, no merge**.

## Seven newly audited Lean 4 declarations

File: `lean/GegenbauerFock/Manuscript14SpecialGramBridge.lean`.

1. `manuscript14_gram_parameter`: exact `1/(4*(1/√2))=1/√8`.
2. `manuscript14Gram_eq_integralLp`: actual `Lp ℂ 2 (Ultraspherical.measure (1/2))` operator `C†C` equals the Bochner exponential integral-kernel operator for every input, not only formal Taylor coefficients.
3. `manuscript14Gram_eq_nuclear_tsum`: equality of bounded operators with the absolutely operator-norm-convergent positive rank-one decomposition.
4. `manuscript14Gram_nuclear_mass_eq_diagonal`: nuclear rank-one mass equals the diagonal exponential integral.
5. `manuscript14Gram_nuclear_mass_eq_kummer`: same scalar equals the Kummer series.
6. `manuscript14Gram_nuclear_mass_eq_uniformIntegral`: identifies the measure exactly as normalized Lebesgue density `du/2` on `(-1,1)` using V007 `Ultraspherical.measure_half_eq_uniformDensity` and rewrites exponent `a*u²`.
7. `manuscript14Gram_basis_trace_eq_kummer`: the complex-Hilbert Gram has the same diagonal trace sum in EVERY orthonormal Hilbert basis.

**Audit:** all seven print only `propext`, `Classical.choice` and `Quot.sound`, no `sorryAx`, no `Lean.ofReduceBool`, no new axioms.

## Provenance

The analytic integral identity, nuclear decomposition and Kummer trace theorems are **existing V007 results**. This module is a precisely typed normalization/application bridge to the printed manuscript 14.1, not a new general Gram/nuclear theorem. The spectral decomposition and operator commutation claimed in manuscript 14.1 remain separate.

## Remaining to close Theorem 6.1 in one kernel

1. Formalize the closed **complex** Legendre operator `D_(1/2)` on its exact weighted spectral domain. The V007 `UltrasphericalSturmLiouvilleRealGraphClosureCore` is on real L². Its genuine complexification is partly available through `UltrasphericalSturmLiouvilleActualComplexLpDecomposition` and `...ActualComplexLpIsometry`, but identification of the full complex spectral domain/closed generator must still be audited.
2. Prove that the genuine exponential Gram operator sends polynomial core elements into this closed domain, and that its second derivatives satisfy the Green integration-by-parts commutation identity as L² vectors.
3. Instantiate the kernel-checked general graph-core / bounded-perturbation theorem from separate [draft PR #32](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/32), matching parameter `a=1/√8`, Hilbert space, domain, quadratic multiplier and integral operator.
4. The precise map `L²→C∞([-1,1])` and its endpoint value `S1(±1)=sinh(a)/a` also require their own complex-L² analytic proof.

**No merge and no manuscript changes.** Parent V007, PR #16, manuscripts 11–13, V097, and `main` remain untouched.
