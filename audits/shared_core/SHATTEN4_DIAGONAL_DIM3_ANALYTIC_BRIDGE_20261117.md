# Shared Schatten–Fredholm core: exact diagonal dimension-three test model

Date: 2026-11-17. **Analytic proof and Lean implementation specification; NOT a Lean certificate, NOT an Arb certificate, and NOT an identification with any manuscript's physical operator.**

Scope: reusable test fixture for M13 (compact spectral approximation), M14 (true regularized Fredholm theory), M15 (determinant/Langevin perturbation), and M16 (the sharp dimension-three Schatten threshold and det₄). The Eulerian M11–M12 layer supplies scalar functions separately; no spurious operator identification is asserted. This is deliberately independent of the Maxwell nearest-mode shell proof in PR #368 and of the M15 squarefree determinant candidate PR #372.

## 1. Concrete compact operator

Let H be the complex Hilbert direct sum of blocks H_n = ℂ^((n+1)(n+2)), indexed n≥0, and let P_n be the mutually orthogonal block projections. Set

    λ_n = 1/(n+2),   m_n = (n+1)(n+2),
    T = ⊕_{n≥0} λ_n I_{H_n}.

The bounded positive selfadjoint T has norm 1/2 and is compact: its finite-block truncations T_{≤N} satisfy ||T-T_{≤N}|| = 1/(N+3) → 0. The nonzero eigenvalues are precisely λ_n, each of multiplicity m_n.

For every real p>0, the diagonal singular-value p-series is

    Σ_{n≥0} m_n λ_n^p = Σ_{n≥0} (n+1)/(n+2)^(p-1).

For n≥0, (n+1)/(n+2) is between 1/2 and 1, so the summand lies between (1/2)(n+2)^(2-p) and (n+2)^(2-p). By the p-series criterion this is finite **if and only if p>3**. In particular T∈S₄ but T∉S₃, T∉S₂ and T∉S₁. This conclusion is for this concrete diagonal model; it is not automatically the Schatten threshold of the actual Maxwell/Dirac resolvent.

## 2. Actual fourth regularized determinant

For each z∈ℂ define the finite-block fourth regularized determinant

    D_{4,N}(z) = Π_{n=0}^N [(1+z λ_n)
                      exp(-z λ_n + z² λ_n²/2 - z³ λ_n³/3)]^(m_n).

This is the genuine finite-dimensional det₄(I+zT_{≤N}) by definition. Define D₄(z)=lim_{N→∞}D_{4,N}(z).

For |w|<1 the exact identity

    log(1+w)-w+w²/2-w³/3
      = Σ_{k=4}^∞ (-1)^(k+1) w^k/k

holds on the branch determined by the power series. For |w|≤1/2,

    |log(1+w)-w+w²/2-w³/3| ≤ |w|⁴/(4(1-|w|)) ≤ |w|⁴/2.

Thus for every R≥0, choose N so that n+2≥2R for all n>N. The logarithmic tail satisfies, uniformly on |z|≤R,

    |Σ_{n>N} m_n [log(1+zλ_n)-zλ_n+z²λ_n²/2-z³λ_n³/3]|
      ≤ (R⁴/2) Σ_{n>N} (n+1)/(n+2)³
      ≤ R⁴/[2(N+2)].

The last bound uses (n+1)/(n+2)³ ≤ 1/(n+2)² and Σ_{n>N}1/(n+2)² ≤ ∫_{N+1}^∞ (x+1)^(-2)dx = 1/(N+2). In particular the product converges locally uniformly to an **entire** function D₄, with D₄(0)=1. The exponential corrections never vanish, and the locally uniformly convergent nonzero tail does not vanish. Therefore D₄ has zeros exactly at z=-(n+2), with multiplicity m_n.

For z away from these zeros, termwise logarithmic differentiation is justified locally uniformly. An exact finite algebraic identity gives

    d/dz log D₄(z)
      = Σ_{n≥0} m_n [1/(n+2+z)-1/(n+2)
                       +z/(n+2)²-z²/(n+2)³]
      = -z³ Σ_{n≥0} m_n/[(n+2)³(n+2+z)].

The second sum converges locally uniformly off the zero set. If |z|≤R and n+2≥2R for n>N, its tail has absolute value at most

    2 R³ Σ_{n>N} m_n/(n+2)^4 ≤ 2 R³/(N+2).

These identities are the **actual diagonal trace formula** once the operator trace is implemented: the operator expression is
    -z³ Tr[T⁴ (I+zT)^(-1)],
defined wherever I+zT is invertible. One must prove equality of this trace with the diagonal series in Lean, not merely assume it from scalar summability.

## 3. Lean 4 proof obligations, in dependency order

1. Construct H as a Hilbert direct sum of finite-dimensional complex blocks; define T using bounded diagonal block maps and prove positivity, selfadjointness, norm 1/2, and the finite-block norm limit.
2. Establish the block eigenvalue/multiplicity theorem and a genuine operator singular-value enumeration. Do **not** identify arbitrary approximation numbers with singular values without the Hilbert compact-operator theorem.
3. Prove the p-series comparison, the iff p>3 threshold for this T, and actual S₄ membership using an appropriate definition of Schatten ideal (not just a surrogate summability claim).
4. Implement finite-dimensional det₄ using the determinant and exponential of finite-block operators, and prove the displayed product from block decomposition.
5. Prove the power-series remainder and the rational uniform tail estimate; obtain local uniform convergence and the entire D₄ via a holomorphic compact-limit theorem.
6. Prove nonvanishing of the infinite tail, zero locations and multiplicities, then justify the differentiated logarithm on the complement.
7. Construct the trace-class T⁴(I+zT)^(-1), prove its trace equals the displayed diagonal sum, and derive the operator trace identity.
8. Add an exact-rational tail-bound test to the shared numerical helper; no FLINT/Arb claim is needed for rational inequalities. Reserve 3,600,000-bit Arb for genuinely transcendental values and verify relative accuracy and decimal rounding cells individually.

## 4. Scope and integration rules

- **PROVED (ordinary mathematical analysis):** the explicit diagonal model, sharp p>3 comparison, locally uniform det₄ product, quantitative tails, and scalar logarithmic derivative above.
- **OPEN (Lean):** all kernel-checked implementation obligations 1–7; no `sorry`, `admit`, or new axioms may be introduced.
- **OPEN (operator bridge):** the identification of the scalar derivative with a genuine Hilbert trace in Lean, and the identification of this test model with the M16 Maxwell/Dirac resolvent. The latter requires independent spectral multiplicities, operator domains and an explicit equivalence.
- **OPEN (numerics):** no Arb run, no 3,400,000-relative-bit claim, no million-digit certificate.
- The analytic model is a **shared regression fixture**, not a substitute for the original manuscript-specific theorems. Preserve all already certified modules; do not modify manuscript text, figures, or protected files.
