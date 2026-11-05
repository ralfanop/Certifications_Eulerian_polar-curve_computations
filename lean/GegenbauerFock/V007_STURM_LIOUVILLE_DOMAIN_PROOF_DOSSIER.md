# V007 — ultraspherical Sturm–Liouville: integral Green identity and domain programme

**Status:** mathematical proof dossier and exact list of Lean obligations.
This file is NOT itself a Lean certificate. Preserve the approved manuscript
V097 and the V007 draft PR #16 unmerged.

## 1. Actual measure and the differential expression

Fix `λ > 0`. Write
`ρλ(x) = cλ (1-x²)^(λ-1/2)` on `(-1,1)`,
where `cλ = Γ(λ+1)/(sqrt(π) Γ(λ+1/2))`.
The existing repository's actual Beta-pushforward probability
measure `Ultraspherical.measure lam` is identified with the
Gamma-normalized density in the separately formalized measure bridge.

On real polynomials, the genuine algebraic differential expression is

`Lλ p = (1-X²)p'' -(2λ+1)Xp'`.

Set `aλ(x)=(1-x²)ρλ(x)=cλ(1-x²)^(λ+1/2)`.
For `-1<x<1`, elementary differentiation gives

`aλ'(x)=-(2λ+1)x ρλ(x)`, and hence
`ρλ(x)(Lλ p)(x)=(aλ(x)p'(x))'`.

The parameter assumption `λ>0` is more than sufficient for
`aλ(x)→0` at both endpoints, because `λ+1/2>0`.
Every polynomial and its derivative are bounded on `[-1,1]`.
All relevant polynomial products and derivatives are integrable.

## 2. Rigorous Green identity on the polynomial core

For any `p,q∈ℝ[X]`, integrate over `[-1+ε,1-ε]` and apply
ordinary integration by parts:

`∫ (Lλ p)(x) q(x) ρλ(x) dx
 = [aλ(x)p'(x)q(x)] - ∫ aλ(x) p'(x)q'(x) dx`.

The boundary term tends to zero as `ε→0+`; the remaining integral
converges (the power `λ+1/2>0` is bounded and continuous up to
the endpoints). Thus

`⟨Lλ p,q⟩_{L²(νλ)}
 = -∫_{-1}^1 aλ(x)p'(x)q'(x) dx
 = ⟨p,Lλ q⟩_{L²(νλ)}`

for real polynomials. After complexifying, insert conjugation on the
appropriate argument in the chosen Mathlib convention.
In particular `⟨Lλ p,p⟩≤0` on the polynomial core.

This *actual integral statement* is a distinct Lean obligation beyond
the already-certified Green moment recurrence and coefficient identities.

## 3. Avoiding an unproved boundary/domain assertion

Let `H=L²(νλ;ℂ)` with the already constructed concrete measure.
Define `D₀` to be the subspace of equivalence classes of complex
polynomial evaluations, **not** all `C²[-1,1]` functions. Define
`A₀:D₀→H` by `A₀[p]=[Lλ p]`.

The preceding definition requires **well-definedness**: if a
polynomial represents the zero `L²` class, then its differential
expression must also represent zero. One possible route uses strict
positivity of `ρλ` on `(-1,1)`, continuity of polynomial evaluations,
and the identity theorem for polynomials: if `[p]=0` then `p=0`
as a polynomial. This gives injectivity of the concrete polynomial
evaluation into `H`.

The operator domain `D₀` is dense, using the existing polynomial
density result, once the exact vector-level identification is built.

## 4. Spectral eigenbasis without guessing a self-adjoint domain

The monomial identity already Lean-certified gives, for `n≥2`,

`Lλ X^n = n(n-1)X^(n-2) - n(n+2λ)X^n`,
and the n=0 and n=1 statements agree with this formula
when the first term vanishes.

Consequently the degree filtration `P_{≤n}` is invariant, and the
leading diagonal coefficient is `-n(n+2λ)`.

Orthogonalize `1,X,X²,...` against the actual strictly positive
weighted `L²` inner product. Because a nonzero polynomial cannot
vanish almost everywhere for this measure, each orthogonalized
polynomial `G_n` has exact degree `n` and positive norm.
Its orthogonality to `P_{≤n-1}`, the symmetry of `A₀`, and
invariance of the filtration imply that `Lλ G_n` is orthogonal to
all `P_{≤n-1}`. Thus it is a scalar multiple of `G_n`, with
scalar determined by the leading monomial coefficient:

`Lλ G_n = -n(n+2λ)G_n.`

The normalized `G_n` form a complete orthonormal Hilbert basis
because real/complex polynomials are dense. In the complex case,
the (G_n) may be taken real-valued and then complexified.

**Lean obligations:** finite-dimensional polynomial-degree filtration,
strictly-positive norm for each nonzero polynomial, Gram–Schmidt
construction or use of existing Mathlib orthogonal-polynomial machinery,
eigenrelations, completeness in the concrete H.

## 5. Essential self-adjointness, closure and resolvent

Let `e_n` be that complete orthonormal eigenbasis and
`d_n=-n(n+2λ)∈ℝ`. The finite-support diagonal operator
on `span_ℂ{e_n}` is symmetric.

For either sign, every basis vector belongs to
`range(A₀±iI)`: its preimage is `(d_n±i)^(-1)e_n`.
The ranges are therefore dense. By the standard deficiency-index
criterion, `A₀` is essentially self-adjoint.

Alternatively, identify its closure explicitly with the diagonal
operator having domain

`D(A) = {f∈H : Σ_n |d_n|² |⟨e_n,f⟩|² < ∞}`

and action `Af=Σ_n d_n⟨e_n,f⟩e_n`.
For `λ>0`, `|d_n|→∞`; every nonreal resolvent is compact
since its eigenvalues `1/(d_n-z)` tend to zero.

**Important:** None of the claims in this section becomes a Lean
certificate merely from proving the formal polynomial Green identity.
The unbounded domain, graph closure, self-adjointness, and compact
resolvent are distinct kernel-checked milestones.

## 6. Existing and new Lean checkpoint boundaries

- General polynomial monomial action: SUCCESS CI 40904636334.
- Quadratic Gegenbauer eigenpolynomial: SUCCESS CI 40907802003.
- Genuine real-linear polynomial differential expression: SUCCESS CI 40918367007.
- Conditional moment Green cancellation: SUCCESS CI 40918915293.
- Actual two-step Beta moment recurrence and high-degree Green
  monomial pair identity: SUCCESS CI 40919430207.
- Low-degree Green pairings: SUCCESS CI 40919907207.
- Unified all-degree monomial Green matrix, full finite polynomial
  coefficient matrix, and genuine integral / polynomial integrability
  bridges: check their dedicated CI results before claiming certification.

The next critical link is to prove a Lean equality between the
actual integral `∫ u, (sturmPolynomial lam p).eval u * q.eval u ∂measure lam`
and the finite coefficient Green matrix. Only then build the genuinely
densely defined operator and its spectral/domain theory.

V007 ONLY. No merge to main; V097 remains unchanged.
