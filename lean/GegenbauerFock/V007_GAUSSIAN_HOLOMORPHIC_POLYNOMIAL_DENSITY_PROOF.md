# V007 — Gaussian holomorphic polynomial density: independent analytic proof

**Status:** rigorous mathematical proof and Lean-formalization contract. **This document is not itself a Lean kernel certificate.** In particular, do not identify the previously certified Gaussian polynomial closure with all Gaussian-L² entire functions until a Lean theorem explicitly makes this identification.

## 1. Non-circular target

Fix `alpha : ℝ` with `0 < alpha`. Let
`dμ_α(z) = (α/π) exp(-α |z|²) dA(z)`
on the genuine complex plane. The existing repository constructs
`gaussianAreaMeasure alpha` and the normalized vectors
`e_n(z) = (α^n/n!)^(1/2) z^n` in `Lp ℂ 2 (gaussianAreaMeasure alpha)`.

Define the **intrinsic** analytic space, independently of polynomial closure,

`H_α = {v ∈ L²(μ_α) | ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ v = [f]_{μ_α}}`.

The proposed theorem is the equality of subsets of genuine Gaussian L²:

`H_α = closure(span_ℂ {e_n | n : ℕ}) = range(coefficientSynthesisL2 alpha ha)`.

The right equality is **already Lean-certified** in
`GaussianAreaCoefficientSynthesisL2.lean`. The first equality is **not yet
Lean-certified**.

## 2. Angular Parseval for an arbitrary entire function

Let `f : ℂ → ℂ` be entire, with Taylor coefficients `a_n` at zero, so

`f(z) = Σ_{n≥0} a_n z^n` for every `z ∈ ℂ`.

For every fixed radius `r ≥ 0`, the Taylor series converges absolutely and
uniformly on `|z| = r`. The functions
`θ ↦ a_n r^n exp(i n θ)` are orthogonal in
`L²([0,2π],dθ/(2π))`. Uniform convergence, or convergence in angular L²,
therefore gives

`(1/(2π))∫₀^{2π}|f(r exp(iθ))|² dθ = Σ_{n≥0}|a_n|² r^(2n).`  (A)

This is a theorem for the *actual entire function*, not an assumption of
polynomial density. Applying exactly the same argument to `f-P_N`, where
`P_N(z)=Σ_{n=0}^N a_n z^n`, yields

`(1/(2π))∫₀^{2π}|f(r exp(iθ))-P_N(r exp(iθ))|² dθ = Σ_{n>N}|a_n|² r^(2n).`  (B)

## 3. Gaussian integration and coefficient identity

The polar-coordinate theorem for planar Lebesgue area, together with the
normalizing density, gives for every nonnegative measurable `g`:

`∫_ℂ g(z)dμ_α(z) = 2α∫₀^∞ r exp(-αr²)
( (1/(2π))∫₀^{2π}g(r exp(iθ))dθ )dr.`

Apply this to `g=|f|²` and insert (A). Tonelli applies **without any
prior assumption of coefficient summability**, because every summand is
nonnegative:

`‖[f]‖²_{L²(μ_α)}
 = Σ_{n≥0}|a_n|² (2α ∫₀^∞ r^(2n+1)exp(-αr²)dr).`

The substitution `t=αr²` and the gamma integral yield

`2α ∫₀^∞ r^(2n+1) exp(-αr²)dr = n! / α^n.`

Consequently,

`‖[f]‖²_{L²(μ_α)} = Σ_{n≥0}|a_n|² n!/α^n.`  (C)

If `f` belongs to the intrinsic space `H_α`, the left side is finite.
Thus the **normalized coefficient sequence**
`c_n = a_n sqrt(n!/α^n)` belongs to `ℓ²(ℕ;ℂ)`.

For the exact repository conventions:
`e_n(z) = sqrt(α^n/n!) z^n`, hence `c_n e_n(z)=a_n z^n`.

## 4. Actual L² convergence of the Taylor polynomials

Apply the polar/Tonelli calculation to (B):

`‖[f]-[P_N]‖²_{L²(μ_α)}
   = Σ_{n>N}|a_n|² n!/α^n → 0`.  (D)

Equation (D) is an explicit **strong L² polynomial density theorem** for
every entire function possessing a Gaussian-L² class. It proves more than
weak density or coefficient orthogonality. Moreover, since the existing
`coefficientSynthesisL2` is an isometric infinite Hilbert sum, and its
canonical basis vectors are the actual `e_n`, the limit in (D) is exactly
`coefficientSynthesisL2 alpha ha c`.

Thus `H_α ⊆ range(coefficientSynthesisL2 alpha ha)`.

## 5. Converse: every ℓ² synthesis has an entire representative

For `c ∈ ℓ²`, set `F_c(z)=Σ_{n≥0}c_n e_n(z)`.
Cauchy–Schwarz gives an absolute bound on each compact disk:

`Σ_n |c_n e_n(z)| ≤ ‖c‖₂ (Σ_n α^n|z|^(2n)/n!)^(1/2)
 = ‖c‖₂ exp(α|z|²/2).`

The same bound uniformly on `|z|≤R` implies locally uniform convergence.
The Weierstrass theorem then makes `F_c` entire. In the existing code,
`OutputComplexHolomorphy.lean` already supplies entire differentiability
for the coefficient evaluation function.

To identify its Gaussian-L² class with `coefficientSynthesisL2 alpha ha c`,
use the following two convergences of the **same finite polynomials**:
(i) strong L² convergence by the already certified Hilbert synthesis
`coefficientSynthesisL2_hasSum`, and
(ii) locally uniform, hence pointwise convergence to `F_c`.
The standard uniqueness of limits in measure (or an a.e.-convergent
subsequence of the L²-convergent sequence) establishes their equality
μ_α-almost everywhere. Thus

`range(coefficientSynthesisL2 alpha ha) ⊆ H_α`.

This direction cannot be bypassed: a closed span of entire polynomials is
not *definitionally* the set of classes with entire representatives.

## 6. Consequences

Combining both inclusions with the already certified closed-span theorem:

`H_α = gaussianPolynomialClosure alpha ha
     = range(coefficientSynthesisL2 alpha ha).`

The space `H_α` is therefore a closed complex Hilbert subspace of true
Gaussian `L²(ℂ)`, and the existing isometry upgrades to an **onto**
`ℓ² ≃ₗᵢ[ℂ] H_α`. It does **not** become onto the whole ambient Gaussian
`L²(ℂ)`, which also contains nonholomorphic functions.

Uniqueness of the entire representative follows from continuity and the
strictly positive Gaussian density: an entire (indeed continuous) function
equal to zero μ_α-a.e. must vanish everywhere, since any point of
nonvanishing has a neighborhood of positive μ_α-measure.

## 7. Exact Lean obligations, in recommended order

1. Formalize the angular Parseval identity (A) and Taylor-tail identity (B)
   for arbitrary `Differentiable ℂ f` and its actual Taylor coefficients,
   without assuming polynomial density. Reuse the already certified
   angular orthogonality modules.
2. Prove the nonnegative Tonelli interchange and radial Gaussian moment
   formula leading to (C). Reuse the existing actual planar measure,
   polar-integrability and monomial-norm modules.
3. Prove (D) in the true `Lp ℂ 2` topology and construct the normalized
   `lp (fun _ : ℕ => ℂ) 2` coefficient vector.
4. Prove that `OutputComplexHolomorphy` evaluation is an a.e. representative
   of true `coefficientSynthesisL2`. Do not replace this with mere pointwise
   series convergence; bridge the L² and pointwise limits explicitly.
5. Define `H_α` intrinsically by existence of an entire representative,
   prove both set inclusions, transfer the closed Hilbert subspace and obtain
   the final surjective isometric equivalence.

**Verification policy:** each Lean theorem must compile at an exact commit
SHA under pinned Lean v4.35.0-rc3 / Mathlib, with explicit `#print axioms`
and no `sorryAx` or `Lean.ofReduceBool`. The mathematical arguments here
are not substitutes for these kernel proofs. Keep PR #16 Draft/unmerged.
Do not modify main, V097, protected V007 handover, or pinned toolchain.
