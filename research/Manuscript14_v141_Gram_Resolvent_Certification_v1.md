# Manuscript 14.1 — §§6–7 formalization ledger v1

**Status checked:** 4 November 2026, Europe/London.  
**Exact manuscript:** `Manuscript_14_v14.1_Cor3.6_Lean4_Arb_CERTIFIED(3).zip`, §6 "The Eulerian Gram operator and its second-order commutant", §7 "Dirichlet determinants, resolvent traces and zeta values".  
**Branch:** `manuscript14-v141-gram-resolvent-20261104`, derived from the corrected Corollary 3.6 branch.  
**Latest SUCCESS:** [CI #41839299668](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41839299668) (**Lean 4 and Arb**), commit `e268edb77448c0c870a1a0be860ea39d04fbb073`.

## 1. Newly kernel-checked Lean results — 9 declarations

Code: `lean/SpecialImaginaryPoint/GramKernelBispectral.lean`.

- `gram_differential_symbol_symmetric`: exact symmetric symbol of the Legendre quadratic perturbation.
- `gram_kernel_symmetric`: symmetry of `exp(a*u*v)`.
- `gram_bispectral_kernel_balance`: full pointwise bispectral kernel multiplier identity.
- `gram_endpoint_flux_plus`, `gram_endpoint_flux_minus`: boundary flux annihilation at ±1.
- `closed_graph_core_commutation`: bounded commutation on any graph core transfers to the entire closed domain, including domain preservation.
- `bounded_perturbation_preserves_graph_core`: graph core for A remains one for A+B when B is bounded.
- `bounded_perturbation_preserves_sequential_closed_graph`: sequential closedness of A survives any bounded linear B.
- `closed_bounded_perturbation_commutation`: combined theorem for A+B on the complete closed domain.

Axiom audits `#print axioms` for all nine declarations show **only** `propext`, `Classical.choice`, `Quot.sound`. No `sorryAx`, no `Lean.ofReduceBool`, no custom postulated operator theorem. The abstract theorems make the core/domain extension fully rigorous **conditionally on the concrete input hypotheses**.

## 2. Newly Arb-verified results — 15 PASS

Code: `numerics/arb/manuscript14_gram_resolvent_arb.py`.  
CI #41839299668, **Arb SUCCESS**: `python-flint==0.9.0`, real-ball precision 256 bits plus Python `Fraction` exact rationals.

- Bernoulli exact rational coefficients `c_m=ζ(2m)/π^(2m)`, m=1,2,3,5.
- Exact rational 34-term alternating series with geometric tail < 10⁻⁶⁰ for the trace of the Dirichlet resolvent at `a²=1/8`, and likewise for the trace of its square.
- Independent interval arithmetic for the Langevin trace expressions, 50–51 decimal-place printed values.
- Eulerian boundary `sinh(1/√8)/(1/√8)` enclosed by positive rational Taylor sum, separated rigorously from Gram's diagonal trace.
- Gram diagonal integral Taylor enclosures and corresponding 30-place interval.

**Important:** these are rigorous scalar enclosures and checks, NOT a kernel-checked construction of the Dirichlet trace-class operator or Fredholm determinant. The exact analytic series identity is already in the written manuscript; the numerical script certifies the values and explicit tails, not the infinite-dimensional operator identity.

## 3. Explicit gap in §6 (Printed Theorem 6.1)

The printed theorem concerns `S_{1/2,a} : L²([-1,1],du/2;ℂ) → L²(...)`,
`a=1/√8`, `D_{1/2}` nonnegative selfadjoint Legendre operator on the
spectral domain `{f: Σ n²(n+1)² |f_n|²<∞}`,
`A_a = D_{1/2} - a² M_{u²}`, and asserts
`S(Dom A_a)⊆Dom A_a` and `A_a S = S A_a`.

**The remaining missing bridge is concrete, not abstract**:
- Identify the complex L² operator and its exact parameter with an already certified V007 Gram (C†C); prove the Kummer mass and basis trace in exactly that normalization. A *separate draft branch* `manuscript14-v141-concrete-gram-v007-20261104` attempts this, drawing on existing `GramIntegralComplete.lean` and `GramNuclearTrace.lean`.
- Link the closed Legendre differential operator on **complex** L² to the existing **real** Sturm polynomial-core certificate (complexification + domains must be verified, not asserted).
- Prove kernel differentiation and two Green integration-by-parts identities on polynomial core for the complex operator and finite special parameter.
- Apply the already kernel-certified `closed_bounded_perturbation_commutation` to actual operators with matched domains. This last application would complete the novel graph-domain commutation claim.

## 4. Explicit gap in §7 (Printed determinant and trace theorems)

- Construct the exact complex Dirichlet Laplacian `A_D=-d²/dt²` with `H²(0,1)∩H¹₀(0,1)` domain; prove spectrum `π²n²` and trace-class inverse.
- Identify Fredholm determinant `det_F(I+x²A_D⁻¹)` with infinite product and `sinh(x)/x` in the actual operator API.
- Prove the zeta-regularized determinant ratio and differentiate logarithmic traces in Lean.
- Prove the exact, not just numerical, series expressions for the first two resolvent traces.

Thus the exact paper statements of **§6 and §7 are not yet fully certified in Lean**. Do not promote conditional core transport or Arb scalar tests into a false full certificate.

## 5. Reuse from previous V007 (not yet imported to this branch)

In branch `gegenbauer-fock-formalization-20261025`:
- `GegenbauerFock.GramIntegralComplete.lean` verifies `gram = gramKernelIntegralLp` on genuine `Lp ℂ 2 (Ultraspherical.measure λ)`;
- `GegenbauerFock.GramNuclearTrace.lean` certifies nuclear rank-one decomposition, exponential diagonal mass, and basis-independent Kummer trace sum;
- `GegenbauerFock.UltrasphericalSturmLiouvilleRealGraphClosureCore.lean` certifies graph-core results on **real** L², not automatically the **complex** Legendre domain of §6.

Source transfer must respect package dependencies and theorem signatures; a new specialization should live in its own draft branch, and no merges will be performed.

## 6. Preservation

Manuscript 14.1 TeX/PDF, manuscripts 11–13, V007 parent, V097, PR #16, and main remain unchanged. All GitHub work is isolated; no merges.
