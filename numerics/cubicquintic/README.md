# Cubic–quintic scheme of Saha et al.: independent check of the coefficient head

R. Saha, A. Li, A. Xue, S. Chaudhuri, A. Klivans, P. K. Kothari and R. Meka, *New Lower and Upper Bounds for the Grothendieck Constant* (arXiv:2608.11158v2), prove

  K_G ≤ π/(2γ) ≤ 1.7818666069360661,  γ = 0.881545409,

with the two-dimensional limiting Krivine scheme

- f(w,x) = sgn(w + ϑ He₃(x)) and g(w,x) = f(w,−x);
- corr(W,W′) = ρ(t) = (t − s₃²t³ + s₅²t⁵)/V and corr(X,X′) = t;
- V = 1 + s₃² + s₅² and ϑ = η/√V;
- η = 0.136419125, s₃ = 0.34101124, s₅ = 0.05276111.

Their proof (Proposition 6.1) uses the near-linearity criterion γ + Δ_H < b₁, where H(t) = Σ b_m t^m and Δ_H = Σ_{m≥3} |b_m|. Their Proposition 6.3 gives three certified inputs:

- b₁ ≥ 0.881573822049;
- Σ_{3≤m≤251} |b_m| ≤ 1.1328860·10⁻⁵;
- ‖D³H‖_{L²(T)} < 14.443, from which the tail is Σ_{m>251} |b_m| ≤ 4.58·10⁻⁶.

This folder recomputes **the first two inputs** independently. It uses our own code, not the authors' scripts, and a different basis and quadrature.

## Method

- **Hermite coefficients.** `alpha.c` is the program of `../heilman3e5`, extended to the profile of this scheme. With the variance-½ variables w = √2 z and x = √2 u, and He₃(√2u) = ψ₃(u), the scheme becomes f = sign(z − a(u)) with a(u) = −(ϑ/√2) ψ₃(u). The program then encloses α_{m,n} for m + n ≤ 251 in Arb ball arithmetic.
  - Gauss–Legendre on [0, 6] with Bernstein-ellipse error bounds.
  - An outer region [6, 10.5], where |a| ≥ 15.
  - A Cramér tail beyond 10.5.
  - The output for the Heilman profile is byte-identical to `../heilman3e5/out/alpha_A_200.txt` (regression test).
- **Correlation function.** `cqhead.c` uses Mehler's formula in each of the two independent coordinate pairs, together with α^g_{m,n} = (−1)^m α^f_{m,n}, to obtain
  H(t) = (π/2) Σ_{m,n} (−1)^m α_{m,n}² t^m ρ(t)^n.
  It then extracts b_k for k ≤ 251 exactly from this finite sum.

## Result (`out/cqhead_251.log`)

| quantity | this check | Saha et al., Prop. 6.3 |
|---|---|---|
| b₁ | 0.8815738220495995485819 ± 1.3·10⁻²³ | ≥ 0.881573822049 |
| Σ_{3≤m≤251, m odd} \|b_m\| | 1.13288599277·10⁻⁵ (upper bound) | ≤ 1.1328860·10⁻⁵ |
| b₁ − γ − head | 1.70841896719·10⁻⁵ | room for the tail |

Both certified inputs agree with ours to all digits they print. The tail Σ_{m>251} |b_m| must stay below 1.708·10⁻⁵; their bound is 4.58·10⁻⁶.

**Inverse series.** The inverse series converges too slowly at γ to be used directly. The partial inverse majorant Σ_{n≤251} |a_n| γⁿ = 0.99998061523306, and the inverse coefficients still have size around 10⁻¹¹ at n = 251. The reason is that H is nearly linear (b₁ − γ ≈ 2.8·10⁻⁵): H⁻¹ is analytic only slightly beyond |w| = γ. The near-linearity criterion is therefore the right route for this scheme.

## Not yet done

The independent bound of the tail Σ_{m>251} |b_m|. It needs boundary values of H, or of its derivatives, on |t| = 1, where the margin of the Gaussian kernel with correlation e^{iθ} is exactly ½.

## Reproduce

```
gcc -O2 -I$FLINT/include alpha.c  -o alpha  -L$FLINT/lib -lflint -lmpfr -lgmp -lm
gcc -O2 -I$FLINT/include cqhead.c -o cqhead -L$FLINT/lib -lflint -lmpfr -lgmp -lm
./alpha cq:0.136419125:0.34101124:0.05276111 251 256 out/alpha_cq_251.txt 60     # ~26 s
./cqhead out/alpha_cq_251.txt 251 256 0.136419125 0.34101124 0.05276111 0.881545409 > out/cqhead_251.log
```
