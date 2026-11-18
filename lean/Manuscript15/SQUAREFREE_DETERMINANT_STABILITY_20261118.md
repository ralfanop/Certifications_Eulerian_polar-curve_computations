# M15 §6.5 — quantitative stability of the squarefree trace-class determinant

This note extends the analytic subcase in PR #372. It is a mathematical proof note, **not** a Lean compilation, FLINT/Arb certification, or an identification of the geometric operator in M15. No numerical precision is claimed.

Let Q be the positive squarefree integers and, for real s>1, let
D_s(z)=∏_{n∈Q}(1+z n^{-s}). Fix σ>1 and real s,t≥σ. For every z∈ℂ,

|D_s(z)-D_t(z)| ≤ |z| |s-t| [-ζ'(σ)] exp(2|z| ζ(σ)).

Here -ζ'(σ)=Σ_{n≥1}(log n)n^{-σ}<∞. In particular s↦D_s is locally Lipschitz as a map from (1,∞) to the space of entire functions with compact-open topology.

**Proof.** The mean value theorem applied to u↦n^{-u} gives
|n^{-s}-n^{-t}|≤|s-t|(log n)n^{-σ}. For a finite F⊂Q, telescope the products:
∏_{n∈F}(1+za_n)-∏_{n∈F}(1+zb_n)
=Σ_{k∈F} z(a_k-b_k) ∏_{n<k}(1+za_n) ∏_{n>k}(1+zb_n),
where F has any fixed increasing ordering, a_n=n^{-s}, b_n=n^{-t}. Taking absolute values and using 1+v≤e^v for v≥0 bounds the difference by
|z| Σ_{k∈F}|a_k-b_k| exp(|z|Σ_{n∈F}(a_n+b_n)).
Each of the two sums in the exponent is at most ζ(σ). Let F increase to Q. Normal convergence of both products on compact z-sets and absolute convergence of Σ(log n)n^{-σ} permit the limit, proving the inequality.

**Uniform truncation.** If D_{s,N}(z)=∏_{n∈Q,n≤N}(1+zn^{-s}), then
|D_s(z)-D_{s,N}(z)|≤|z| exp(2|z|ζ(s)) Σ_{n>N}n^{-s}
≤ |z| exp(2|z|ζ(s)) N^{1-s}/(s-1).
The same finite-product telescoping argument applies with the missing coefficients set to zero, and the last inequality is the integral test.

**Scope boundary.** These are unconditional analytic estimates for the explicit diagonal squarefree model only. They do not prove the manuscript's operator identification, regularized determinants, or any 3,600,000-bit numerical statement. Lean obligations remain open until compiled on an exact HEAD with its CI recorded.
