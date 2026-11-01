# V007 — explicit all-degree Gegenbauer eigenbasis and exact spectral closure

**Scope:** mathematical derivation and Lean implementation specification;
**NOT** an additional Lean certificate. The actual certified graph,
resolvent, and polynomial-eigenmode lemmas live in the corresponding
`UltrasphericalSturmLiouvilleReal*.lean` modules. Keep PR #16 draft,
V097 and main unchanged.

## 1. Construct monic eigenpolynomials with finite scalar recurrences

Fix `λ > 0` and `n : ℕ`. Set `m = n / 2` (natural-number division).
Define coefficients `a(n,0)=1` and, for `0 ≤ k < m`,

```text
a(n,k+1) =
  -(n-2k)(n-2k-1) / (4(k+1)(n-k-1+λ)) * a(n,k).
```

Each denominator is strictly positive under the indicated bounds,
because `n-k-1 ≥ 1` whenever `0 ≤ k < ⌊n/2⌋` with `n ≥ 2`.
Define the finite real polynomial

```text
G_{n,λ}(X) = ∑_{k=0}^{⌊n/2⌋} a(n,k) * X^(n-2k).
```

Its leading coefficient is exactly one and its degree exactly `n`.
The initial examples are

```text
G_0 = 1;
G_1 = X;
G_2 = X² - 1/(2(λ+1));
G_3 = X³ - 3X/(2(λ+2)).
```

This normalization avoids Gamma functions and a priori orthogonal
polynomial libraries.

## 2. Verify the exact eigenrelation by finite telescoping

The already kernel-certified monomial identity is

```text
L_λ X^j = j(j-1)X^(j-2) - j(j+2λ)X^j.
```

Put `d_j=-j(j+2λ)`. For `k≥1`, the coefficient of
`X^(n-2k)` in `(L_λ-d_n)G_{n,λ}` is

```text
4k(n-k+λ)*a(n,k)
  + (n-2k+2)(n-2k+1)*a(n,k-1),
```

because `d_{n-2k}-d_n=4k(n-k+λ)`. By the
recurrence this expression is zero. The leading term cancels
identically, and the final lower shift vanishes for exponent 0 or 1.
Thus

```text
sturmPolynomial λ (G n λ) = sturmEigenvalue λ n • (G n λ).
```

Use a finite-sum shift/reindex lemma in Lean. This proof needs no
unbounded-operator spectral assumptions.

## 3. Orthogonality, completeness, spectral diagonalization

The actual weighted-real-L² Green identity on polynomial vectors is
already certified. Apply it to `G_n,G_m`:

```text
(d_n-d_m) * ⟨[G_n],[G_m]⟩ = 0.
```

Distinct degrees give distinct eigenvalues for `λ>0`, so the vectors
are orthogonal. Nonzero monic polynomials have positive L² norm because
the ultraspherical measure is strictly positive on the open interval.
Normalize to `e_n=[G_n]/‖[G_n]‖`.

The monic triangular structure gives
`span{G_0,...,G_n}=ℝ[X]_{≤n}`. Existing genuine polynomial density
in weighted L² implies `(e_n)_{n∈ℕ}` is a complete orthonormal Hilbert
basis. No circular assumption of completeness is allowed.

The corresponding diagonal multiplication operator has domain

```text
D_diag = {f : H | ∑_n d_n² |⟨f,e_n⟩|² < ∞}
```

and action `D_diag f = ∑_n d_n⟨f,e_n⟩e_n`.
Show it is closed by coordinatewise convergence under graph limits.

The finite spectral truncations `p_N=∑_{n≤N}⟨f,e_n⟩e_n` are real
polynomials and satisfy

```text
‖f-p_N‖² + ‖D_diag f-L₀ p_N‖²
 = ∑_{n>N}(1+d_n²)|⟨f,e_n⟩|² → 0.
```

Thus the polynomials form a **graph core** of the diagonal realization,
and the closed diagonal graph equals the canonical polynomial graph
closure (both inclusions). Equivalently, invoke the already
kernel-certified `sturmRealPartialOperator_spectral_eq_closure_of_nonpositive`
once closedness, polynomial extension and nonpositivity of `D_diag`
are shown.

The exact positive resolvent then acts diagonally by

```text
R_t e_n = (t+n(n+2λ))⁻¹ e_n,  t>0,
```

agreeing with the full-real-L² resolvent previously certified from
the finite polynomial inverse.

## 4. Lean tasks, in dependency order

1. `sturmMonicCoeff`: finite recurrence, positivity of denominators,
   leading coefficient, and the coefficient cancellation identity.
2. `sturmMonicEigenPolynomial`: finite sum and exact all-degree
   polynomial eigenequation (using the certified monomial rule).
3. Real weighted-L² nonzero norms; polynomial eigenorthogonality using
   the existing Green theorem.
4. Triangular polynomial spanning; Hilbert orthonormal basis and
   completeness using already certified L² polynomial density.
5. Diagonal unbounded `LinearPMap` and precise weighted-ℓ² domain,
   closed graph and finite-truncation graph convergence.
6. Exact graph, domain and action equality with the canonical closure;
   explicit (R_t) spectral eigenvalues.

**Certification boundary:** Finite-degree monomial action, dense
polynomial domain, the canonical closed graph, full positive resolvent
and the closed/resolvent graph equality are certified in the previously
green workflows. The all-degree eigenpolynomial construction, Hilbert
basis, and diagonal operator still require Lean compilation and
`#print axioms` verification. Do not label them certified until then.
