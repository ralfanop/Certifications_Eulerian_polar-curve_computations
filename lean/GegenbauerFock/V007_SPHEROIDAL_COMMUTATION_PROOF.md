# V007 — spheroidal Gram commutation: certified kernel and remaining graph obligations

Status: 2 November 2026. Independent V007 research branch (PR #16, Draft).
This document does **not** claim a closed-operator commutation theorem.

## What is genuinely kernel certified

The source module [`SpheroidalExponentialBispectral.lean`](SpheroidalExponentialBispectral.lean)
at commit `dfe243ecb5188a1e2db0dfc82f13adfd44e18b26`
has five theorems kernel-checked by
[CI #41438697156](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41438697156)
(SUCCESS, 9,013 jobs; only `propext`, `Classical.choice`, `Quot.sound`).

For any real `λ,c,u,v`, let `K_c(u,v)=exp(cuv)`, and
`D_λ=-(1-u²)d²/du²+(2λ+1)u d/du`.
With `A_{λ,c}=D_λ-c²M_{u²}`,

`(A_{λ,c}^{(u)}K_c)(u,v)=(A_{λ,c}^{(v)}K_c)(u,v)`.

The proof uses true Mathlib first and second real derivatives.
It does not invoke unproved symbol-level derivative substitutions.
In the manuscript the Gram parameter is `c=1/(4α)`, `α>0`.

## What remains for operator commutation

1. **Exact identification of the integral Gram and intrinsic operator.**
   Using the actual, nonformal ultraspherical Beta-pushforward measure,
   certify the bounded integral operator
   `(S_{λ,c}f)(u)=∫ exp(cuv) f(v) dν_λ(v)`.
   Identify it with the actual source Gram `C_{λ,α}* C_{λ,α}` at
   `c=(4α)⁻¹` by an equality of bounded operators, not just their
   quadratic forms or their traces. Existing Fock Gram pairing
   lemmas and kernel formulas should be reused after checking their types.

2. **Graph regularity / invariance.** For `λ>0`, prove
   `S_{λ,c}(L²(ν_λ)) ⊆ Dom(\bar D_λ)` (or enough invariance on the
   perturbed domain). One constructive route uses the entire expansion
   `S f(u)=∑_{n≥0} cⁿuⁿ/n! · ∫vⁿf(v)dν_λ(v)`.
   Because `|∫vⁿf|≤‖f‖₂` and the Sturm differential action on `uⁿ`
   has at most quadratic growth in n, polynomial partial sums converge
   in the canonical closed graph norm. This avoids asserting that all
   smooth functions automatically belong to the selected closure.

3. **Weighted Green identity on the polynomial core.** With
   `w_λ(u)=const·(1-u²)^(λ-1/2)`, and
   `p_λ(u)=(1-u²)w_λ(u)=const·(1-u²)^(λ+1/2)`,
   `D_λ f=-w_λ⁻¹(p_λ f')'` on `(-1,1)`.
   The Green boundary form is
   `[p_λ(u)(f(u)g'(u)-f'(u)g(u))]_{-1}^{1}`.
   Its endpoint vanishing needs an explicit argument for the function
   classes used, including exponentials with bounded first derivative;
   it is *not* automatic for arbitrary L² representatives.
   Because `λ>0`, `p_λ(±1)=0` by a positive-power limit.

4. **Dense-core commutation.** For polynomials `f`, justify
   differentiation under the integral, use the certified pointwise
   bispectral identity, and move `D_λ` in the integration variable by
   the weighted Green identity. The bounded potential is multiplication
   by `-c²u²`; retain its negative sign throughout.

5. **Extension to the closed domain.** Since the polynomial Sturm graph
   is certified to be a core of its exact selfadjoint spectral
   realization on weighted real L², approximate
   `f∈Dom(\bar A_{λ,c})` in graph norm by polynomial `f_n`.
   The integral Gram is bounded and graph invariance from step 2 gives
   `A S f=S A f` by closedness. Prove domain invariance explicitly.
   For the manuscript's *complex* L² source, supply either an independent
   complexification proof or the corresponding complex closed spectral
   realization; a real-L² theorem alone does not silently imply it.

## Exact distinction

The kernel balance is **COMPLETE in Lean**.
The equality `A_{λ,c} S_{λ,c}=S_{λ,c} A_{λ,c}`
on the domain of the canonical unbounded Sturm closure is
**NOT certified yet**. In particular, equality of differential
expressions does not determine an unbounded operator's domain.

No merge with V097 or V170 is authorized.
