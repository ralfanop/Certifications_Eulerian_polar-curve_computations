# Heilman's 2D graph-threshold profiles: a rigorous certificate for K_G ≤ K_Kr − 3·10⁻⁵

S. Heilman, *An upper bound on Grothendieck's constant* (arXiv 2606.00247), proposes two rounding functions

  f(x₁,x₂) = sign(x₂ − a(x₁)),  g(y₁,y₂) = sign(y₂ − b(y₁)),

where a and b are odd Hermite expansions through h₁₀₁, with 51 decimal coefficients each. His script `verify_best_2d_graph_threshold_improvement.py` (repository sheilman77/grothendieck_upper_bounds) checks the improvement K_Kr − π/(2γ_N) > 3·10⁻⁵ in floating point only, and says so: "not a rigorous interval certificate".

This folder certifies the claim rigorously.

**Result.** For Heilman's profiles, taken as exact decimals:

- **K_G ≤ K_Kr − 3·10⁻⁵**, with margin 1 − A(γ_t) ≥ 7.8775·10⁻⁷.
- More precisely, **K_G ≤ 1.782182847509648 = K_Kr − ε** with ε ≥ 3.1130681721·10⁻⁵.
- The bound that these profiles give through Heilman's method is K_Kr − ε* with 3.1130681721·10⁻⁵ < ε* < 3.1130693777·10⁻⁵. Heilman's floating-point value is 3.1131·10⁻⁵.

Here K_Kr = π/(2 log(1+√2)) = 1.7822139781913691… is Krivine's constant.

## Method

**1. Framework** (Krivine; Braverman–Makarychev–Makarychev–Naor; Heilman, Cor. 1.3)
- H(z) = (π/2)·E[f(Gu)g(Gv)] with ⟨u,v⟩ = z, so H(z) = Σ C_k z^k, C_k = (π/2) Σ_{m+n=k} α^f_{m,n} α^g_{m,n}.
- The α are the coefficients in the orthonormal Hermite basis for the weight e^{−x²}/√π:
  - α_{m,n} = ∫ψ_m(u) I_n(a(u)) dμ(u);
  - I₀ = −erf(a), I_n = √(2/(πn)) e^{−a²} ψ_{n−1}(a).
- Let b_n be the coefficients of H⁻¹ and A(c) = Σ|b_n|cⁿ. If A(c) ≤ 1 and c lies inside the disk of convergence of H⁻¹, then K_G ≤ π/(2c). For A(c) < 1, pad the vectors with orthogonal components.
- The target is γ_t = π/(2(K_Kr − 3·10⁻⁵)) = 0.88138842342697….
- Sanity check: f = g = sign(x₁) gives H = arcsin and recovers Krivine's constant.

**2. Rigorous α_{m,n}, m + n ≤ 200** (`alpha.c`, FLINT/Arb ball arithmetic, precision 256). The integrand is even, so integrate over [0, ∞) and double.
- **On [0, 4.5]:** 45 subintervals with exact rational centres (2s+1)/20 and half-width 1/20, each with 60-point Gauss–Legendre. The error bound is h·(64/15)·M·ρ^{−(2P−2)}/(ρ²−1) (Trefethen, ATAP Thm 19.3). M is computed on balls covering Bernstein ellipses, for ρ ∈ {1.25, 1.6, 2.2, 3.5}.
- **On [4.5, 9]:** cells with |a| ≥ 15 throughout reduce to I₀ = ∓(1 − erfc|a|), with |I_n| ≤ e^{−112} for n ≥ 1. Cells containing roots of a, of width < 2·10⁻⁸, go entirely into the radius.
- **Beyond 9:** Cramér's inequality |ψ_m|e^{−u²/2} ≤ 1.0865.
- **Outcome:** radii are about 3·10⁻¹⁹ for small indices and at most 1.4·10⁻¹⁵.

**3. Finite part** (`certify.c`)
- C_k for k ≤ 200: even ones vanish identically, and C₁ = 0.99812012667919862….
- Parseval check: Σ_{k≤200} S_k = 0.96400….
- b_n for n ≤ 200, by series reversion.
- A₂₀₀(γ_t⁺) = 0.99999921224500 ± 7·10⁻¹⁵.

**4. Tail** (Rouché, `certify.c`, `mbound.c`)

Notation: E = H − arcsin, φ(ζ) = E(sin ζ), G(ζ) = H(sin ζ) = ζ + φ(ζ).

- **Analytic continuation of E.** E continues analytically through
  E(z) = (π/2)∫∫ p_z(u,v) [erf a(u) · erf b(v) + 2∫₀^z (p_t(a,b) − p_t(0,0)) dt] du dv,
  where p_z = e^{−Q}/(π√(1−z²)) and Q = (u²+v²−2zuv)/(1−z²). This holds wherever the margin m(t) = Re w − |Re(tw)|, w = 1/(1−t²), is positive along [0, z].
- **Starlike image and margins on ρ' = 1.10** (`mbound.c`, certified):
  - sin(disk ρ') is starlike, since Re(ζ cot ζ) ≥ ρ' cot ρ' = 0.5599 > 0;
  - |Re sin ζ| ≤ 0.94567 < 1;
  - every segment [0, sin ζ] has margin ≥ 0.184.
- **Profile-independent bound** (holds for any profiles):
  |E(z)| ≤ (π/2)|1−z²|^{−1/2} m(z)^{−1} (1 + (4|z|/π) sup_{[0,z]}|1−t²|^{−1/2}),
  which gives M' := sup_{|ζ|=1.10}|φ| ≤ 23.077. The Lean check uses 23.1.
- **Bound on φ at s = 1.02:**
  - The φ_j are exact from the e_k = C_k − arcsin_k for k ≤ 200.
  - The sup over |ζ| = 1.02 of |Σ_{j≤200} φ_j ζ^j| is at most 0.0050387 (4000 arcs plus a derivative bound).
  - The Cauchy tail is M'(s/ρ')²⁰¹/(1 − s/ρ') = 8.14·10⁻⁵.
  - Hence δ ≤ 0.0051201.
- **Inverse function.** Rouché gives G⁻¹ analytic on |w| < s − δ, with |G⁻¹| < s. Since H⁻¹ = sin∘G⁻¹, we get |b_n| ≤ sinh(s)/R'ⁿ with R' = 1.0148799.
- **Tail sum.** Σ_{n>200} |b_n| γ_tⁿ ≤ sinh(s) q²⁰¹/(1−q) = 4.48·10⁻¹², with q = 0.86847.

**5. Closing step** (`closing.py`, Lean)
- Exact rational re-evaluation of every final inequality from the exported bounds (`out/bounds.txt`):
  - ⌈·⌉ and ⌊·⌋ of |b_n| to 40 decimals;
  - the polynomial sup;
  - M'.
- asinh 1 and sinh(1.02) are bounded from their series.
- Bisection on γ encloses the root c* of A(c) = 1 in (0.881388982611894, 0.881388982617856).
- `lean/Heilman/Heilman3e5Closing.lean` checks the same 20 statements in the Lean kernel (`decide +kernel`). It uses core Lean 4 only and depends on no axioms. The log is `Heilman3e5Closing.log` (Lean 4.35.0, about 2 s).
- The only outside input is π ∈ (3.14159265358979323846, 3.14159265358979323847), Mathlib's `Real.pi_gt_d20` and `Real.pi_lt_d20`.

## What is and is not covered

- The certificate is for the profiles as published: the 51 + 51 decimal coefficients, read as exact rationals (`profile_A.txt` and `profile_B.txt` are verbatim copies).
- The framework theorem itself is taken from the literature. That is the Krivine-type bound K_G ≤ π/(2c) when Σ|b_n|cⁿ ≤ 1. The analytic facts used in step 4 are proved in the comments of `certify.c` and `mbound.c` and summarised above.
- `cbound.c` gives a sharper bound, sup|φ| ≤ 0.73 on |ζ| = 1.10, but it sums cells in double precision. It is **not** used in the chain; the profile-independent `mbound.c` is used instead. The result has room for M' up to about 750.
- An independent audit compared α_{m,n} and C_k with mpmath values (tanh–sinh quadrature at 34 digits, split at the roots of a). It found a grid-tiling defect and an off-by-two exponent in the quadrature bound. Both are corrected, and all spot values now lie inside their balls with distance/radius ≤ 10⁻⁴.

## Reproduce

```
CC="gcc -O2 -I/path/to/flint/include -L/path/to/flint/lib -lflint -lmpfr -lgmp -lm"   # FLINT 3.3.1
$CC alpha.c -o alpha; $CC certify.c -o certify; $CC mbound.c -o mbound
./alpha profile_A.txt 200 256 out/alpha_A_200.txt          # ~12 s each
./alpha profile_B.txt 200 256 out/alpha_B_200.txt
./mbound 1.10 2000 256 128 > out/mbound.log
./certify out/alpha_A_200.txt out/alpha_B_200.txt 200 256 200 1.02 1.10 23.1 3e-5 out/bounds.txt > out/certify.log
python3 closing.py --lean ../../lean/Heilman/Heilman3e5Closing.lean > out/closing.log    # 17/17
lean ../../lean/Heilman/Heilman3e5Closing.lean                                          # 20 theorems, no axioms
```

| File | Content |
|---|---|
| `alpha.c` | Rigorous Hermite coefficients α_{m,n} of one profile |
| `certify.c` | C_k, b_n, A_N, φ_j, polynomial sup, δ, tail, enclosure of c*; exports `out/bounds.txt` |
| `mbound.c` | Profile-independent bound M' and the strip, margin and starlikeness checks |
| `closing.py` | Exact rational closing step; generates the Lean file |
| `cbound.c` | Sharper double-precision bound of sup|φ| (diagnostic only) |
| `show.c` | Prints an α file |
| `out/` | α enclosures (prec 256, `arb_dump_str`), logs, exported bounds |
