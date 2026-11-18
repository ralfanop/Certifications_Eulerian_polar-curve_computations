# Shared 11–16: exact Schatten moments and det4 Taylor invariants

Date: 2026-11-18. Independent analytic extension of the **diagonal test model** in Draft PR #373, not a claim about any Maxwell/Dirac/Gegenbauer operator. Does not modify the manuscripts, figures, or existing Lean modules.

## Model and exact trace moments

Let H = ⊕_{n≥0} ℂ^{(n+1)(n+2)} and let T act as multiplication by λ_n=1/(n+2) on the n-th block, of dimension m_n=(n+1)(n+2). For every **real s>3**, the positive diagonal spectral sum is

    M(s) := Σ_{n=0}^∞ m_n λ_n^s
          = Σ_{k=2}^∞ [(k-1)k/k^s]
          = Σ_{k=2}^∞ [k^{2-s}-k^{1-s}]
          = ζ(s-2)-ζ(s-1).

Both zeta series converge absolutely for s>3. This is an exact equality of convergent real series. For integer q≥4, the **ordinary Hilbert-space trace** Tr(T^q) equals M(q) by the standard trace formula for a positive diagonal trace-class operator. This last identification is mathematically justified by the orthonormal block basis, but is NOT YET implemented as a Lean operator trace.

In particular

    Tr(T^4) = ζ(2)-ζ(3) = π²/6 - ζ(3) > 0.

The positivity follows termwise from (k-1)/k^3>0. This identity supplies a rigorous, independent regression invariant for the det4 construction; Arb can certify numerical values of ζ(3), but Arb cannot replace the infinite-series proof.

## Exact Taylor germ of the fourth regularized determinant

Let D₄(z) denote the entire function defined by the locally uniformly convergent regularized product in PR #373:

    D₄(z) = Π_{n≥0} [(1+zλ_n) exp(-zλ_n+z²λ_n²/2-z³λ_n³/3)]^{m_n}.

For |z|<2, since sup_n λ_n=1/2, the principal logarithm of each factor admits an absolutely summable expansion. More explicitly, for every 0<r<2,

    Σ_{q=4}^∞ (r^q/q) M(q)
      ≤ (r^4/4) M(4) / (1-r/2),

because λ_n^{q} ≤ 2^{-(q-4)} λ_n^4. Tonelli/absolute convergence therefore permits interchanging the spectral and Taylor sums, uniformly on |z|≤r. Thus

    log D₄(z) = Σ_{q=4}^∞ (-1)^{q+1} M(q) z^q/q
              = -[ζ(2)-ζ(3)] z⁴/4 + [ζ(3)-ζ(4)] z⁵/5 - ...

This identity is valid on |z|<2 with log D₄(0)=0; it is **not** a global single-valued logarithm across zeros. In particular

    (log D₄)^{(j)}(0)=0  for j=1,2,3,
    (log D₄)^{(4)}(0)=-6[ζ(2)-ζ(3)],
    D₄^{(4)}(0)=-6[ζ(2)-ζ(3)].

The last equality follows because the first three derivatives of log D₄ vanish. Equivalently

    D₄(z)=1-[ζ(2)-ζ(3)] z⁴/4+O(z⁵).

The derivative identity in PR #373 has the independent local check

    d/dz log D₄(z)=-z³ Σ_{n≥0} m_n/[(n+2)^3(n+2+z)]
                  =-[ζ(2)-ζ(3)]z³+O(z⁴).

The remainder is controlled by the same absolutely convergent spectral majorant; no numerical equality is inferred from overlapping intervals.

## Reuse and precise open obligations

* **M11–12:** exact Eulerian scalar identities remain independent; these spectral moments must not be relabeled as Eulerian identities without an explicit proved bridge.
* **M13:** reusable regression fixture for a compact operator and its Schatten power sums; no identification with Gegenbauer–Fock singular values.
* **M14–15:** tests for trace-vs-determinant and logarithmic derivative interfaces; no replacement for genuine Dirichlet differential domains or Gibbs/Wasserstein arguments.
* **M16:** sharp p>3 test fixture and det4 fourth-order invariant; no Maxwell/Dirac spectral equivalence.
* **OPEN Lean:** implement block Hilbert direct sum, positive compact T, genuine trace-class T^q and its trace formula, real zeta summability and difference identity, locally uniform Taylor exchange, and analytic derivative. The finite algebraic cancellation in PR #375 is separately **PROVED (Lean, exact HEAD)**; this new analytic note is not.
* **OPEN FLINT/Arb:** optional zeta-value interval regression at 3,600,000 working bits with >=3,400,000 verified relative bits and strict 1,000,001-significant-digit rounding-cell inclusion. No such run is claimed.
* **OPEN integration:** compare this fixture to manuscript-specific operators only after a proved spectral equivalence. No automatic merge.

**Status:** PROVED by the explicit mathematical series argument above; CONDITIONAL for integration; OPEN for Lean/Arb certification. No CI, commit-head kernel check, or Arb result is claimed by this note.
