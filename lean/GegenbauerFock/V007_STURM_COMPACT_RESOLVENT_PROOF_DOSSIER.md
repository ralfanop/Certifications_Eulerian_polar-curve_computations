# V007 — Compact resolvent of the closed Gegenbauer–Sturm operator

## Status and certification boundary (2 November 2026)

**COMPLETE: exact real weighted-L² Sturm resolvent compactness is
kernel-certified.** This Markdown exposition is not itself a Lean
certificate. The unconditional Lean theorems and their axiom audits
are in `UltrasphericalSturmLiouvilleResolventCompactExact.lean`.

- [Final CI #41429342198](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41429342198):
  **SUCCESS**; 9,098 jobs; exact spectral truncation operator norm
  (`sturmRealClosedResolvent_finite_tail_norm_eq`) and unconditional
  compactness (`sturmRealClosedResolvent_isCompactOperator`).
- [Uniform operator-norm upper bound #41429311807](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41429311807):
  **SUCCESS**, `sturmRealClosedResolvent_finite_tail_norm_le`.
- [Exact Hilbert Fourier coordinates #41429302314](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41429302314):
  **SUCCESS**.
- [Genuine rank-N truncation compactness #41427284868](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41427284868):
  **SUCCESS**.
- [Conditional compactness bridge #41428087599](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41428087599):
  **SUCCESS**, and its hypothesis is discharged in the final theorem.

The final `#print axioms` reports only the standard
`propext`, `Classical.choice`, and `Quot.sound`: no `sorryAx`
or `Lean.ofReduceBool`. Pinned Lean v4.35.0-rc3 / Mathlib.

## Statement

Fix λ>0 and t>0. In the genuine real ultraspherical Hilbert space

    H_λ = L²(ν_λ; ℝ),

let A_λ be the canonical closure of the polynomial Sturm–Liouville
operator

    L_λ p(u) = (1-u²)p''(u) − (2λ+1)u p'(u).

Let {e_n : n∈ℕ} denote the **explicit normalized Gegenbauer
eigenpolynomials**, already proved complete and orthonormal in H_λ.
Their eigenvalues are −d_n, with

    d_n = n(n+2λ),  d_n≥0.

Write R_t = (tI − A_λ)⁻¹ for the actual bounded positive-shift
resolvent of the canonical closure. Its certified action is

    R_t e_n = β_n e_n,    β_n = 1/(t+d_n).

In particular β_n>0, β_n is strictly decreasing, and β_n→0.

For N∈ℕ, define the finite-rank spectral truncation

    T_N f = ∑_{n=0}^{N−1} β_n ⟨e_n,f⟩ e_n.

Then

    ‖R_t−T_N‖ = β_N = 1/(t+N(N+2λ)) → 0.

Consequently R_t is a compact operator on the **actual weighted real
L²**, not merely on an abstract spectral sequence model.

## Proof of the operator-norm identity

Let f∈H_λ and put a_n=⟨e_n,f⟩. The established Hilbert-basis
equivalence gives a∈ℓ² and Parseval:

    ∑_{n≥0}|a_n|² = ‖f‖².

Because R_t is bounded and diagonal on all the actual Fourier
coefficients, the L²-convergent reconstruction yields

    R_t f = ∑_{n≥0} β_n a_n e_n.

By construction, T_N f is the finite partial sum. Thus

    (R_t−T_N)f = ∑_{n≥N} β_n a_n e_n.

Parseval and monotonicity give

    ‖(R_t−T_N)f‖²
      = ∑_{n≥N} β_n²|a_n|²
      ≤ β_N² ∑_{n≥N}|a_n|²
      ≤ β_N² ‖f‖².

Therefore ‖R_t−T_N‖≤β_N.

For the converse inequality take the normalized basis vector f=e_N,
with ‖e_N‖=1. Since its degree N is excluded from T_N,

    T_N e_N=0,  R_t e_N=β_N e_N.

Therefore ‖(R_t−T_N)e_N‖=β_N, giving the reverse operator-norm
inequality and hence equality.

The scalar decay β_N→0 establishes convergence T_N→R_t in the
operator norm. Each T_N is a finite sum of rank-one bounded operators
and therefore compact. Compact operators are norm-closed for complete
target spaces. It follows that IsCompactOperator R_t.

## Mathematical consequences

1. **Compact resolvent:** R_t is compact for each t>0.
2. **Discrete spectral representation:** The canonical closed
   differential realization has eigenvalues −n(n+2λ), n∈ℕ, with
   the explicit complete normalized Gegenbauer eigenbasis.
3. **Exact finite-truncation error:** ‖R_t−T_N‖=β_N.
4. **Quadratic rate:** for N≥1,
   β_N≤N⁻²; this follows from d_N≥N² for λ>0.
5. **No hidden spectral-extension assumption:** The operator and
   domain were identified with the canonical closure in
   UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure.lean.

## Completed Lean obligations and scope

The concrete normalized complete Gegenbauer Hilbert basis, genuine closed
resolvent's diagonal coefficients, finite-rank compactness, exact finite
coefficient cutoff, sharp upper and lower norm-tail bounds, norm equality,
and compact limit are proved with kernel-checked declarations.

No additional Lean obligation remains for the two final real weighted-L²
resolvent theorems above. Complex Fock operators, Gram operators and
Schatten-ideal claims are distinct objects and remain subject to their
own independent verification.

**Repository restrictions:** PR #16 remains Draft and unmerged. No changes
to main, V097 or V170.
