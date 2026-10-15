# Bochner (1929), p. 733: check of two printed formulas

Source: S. Bochner, *Über Sturm-Liouvillesche Polynomsysteme*, Math. Z. **29** (1929) 730–736, DOI 10.1007/BF01180560. We read the GDZ scan of volume 29 (PPN002370980), where p. 733 is page 738 of the volume PDF. The same text appears in the Springer scan.

Status: **certified by us** (exact integer and rational arithmetic, `bochner733_check.py`, log `bochner733_check.log`, 15 Oct 2026).

## (A) The Hermite sum

Bochner prints

  Pₙ(x) = Σ_{ρ=0}^{[n/2]} (−1)^ρ C(2ρ,ρ) C(n,2ρ) (2x)^{n−2ρ}

and calls it the Hermite polynomials, i.e. the polynomial solutions of y″ − 2xy′ + 2ny = 0. The Hermite coefficients are n!/(ρ!(n−2ρ)!), and

  n!/(ρ!(n−2ρ)!) = C(2ρ,ρ) · C(n,2ρ) · ρ!.

The printed sum therefore lacks the factor ρ!. It agrees with Hₙ for n ≤ 3 only (ρ! = 1 for ρ ≤ 1). From n = 4 on the printed polynomials do not solve the Hermite equation, for even and odd n alike. For example:

- printed P₄ = 16x⁴ − 48x² + 6, while H₄ = 16x⁴ − 48x² + 12;
- printed P₅ = 32x⁵ − 160x³ + 60x, while H₅ = 32x⁵ − 160x³ + 120x.

Exact residuals for n ≤ 20 are in the log. The corrected sum

  Hₙ(x) = Σ_{ρ=0}^{[n/2]} (−1)^ρ C(2ρ,ρ) C(n,2ρ) ρ! (2x)^{n−2ρ}

retains the central binomial coefficients C(2ρ,ρ), the type-B Catalan numbers.

## (B) The transformation of Normalform 2 (corrected 15 Oct 2026)

Normalform 2 (p. 732) is y″ + (δ + εx)y′ + λy = 0. Bochner prints

  ξ = δ√(−1/(2ε)) + √(−ε/2)·x.

Put ξ = a + bx with b² = −ε/2. After division by b², the coefficient of y_ξ is −2ξ + (δ − εa/b)/b. The Hermite form needs a = δb/ε, and since (b/ε)² = −1/(2ε), Bochner's coefficient √(−1/(2ε)) must equal b/ε. With principal square roots:

- **ε > 0.** b = i√(ε/2) and √(−1/(2ε)) = i/√(2ε) = b/ε. Bochner's formula is exactly right, and ξ is complex. For ε = 1, both coefficients equal

    z₀ = √(−1/2) = i/√2,  so ξ = z₀(δ + x).

- **ε < 0** (real ξ, the case of orthogonality on the real line). b = √(−ε/2) > 0, while b/ε < 0. The two roots must then carry opposite signs, ξ = −δ√(−1/(2ε)) + √(−ε/2)·x. Read with positive real roots, the printed form leaves y_ξξ − 2(ξ − 2a)y_ξ + λ′y = 0.

So the formula is correct in the complex reading. The earlier version of this note called it wrong, but it is so only when both roots are taken real and positive for ε < 0. The two admissible real choices differ by ξ → −ξ, which multiplies Hₙ by (−1)ⁿ, i.e. it changes the sign of the odd-degree polynomials only. The script checks both signs of ε exactly, in Gaussian rationals, with ε = ±2k² and k = 1, 2, 3.

The constant z₀ = i/√2 = √(−1/2) also satisfies z₀² = −1/2 = ζ(3)/ψ⁽²⁾(1). Since ψ⁽ⁿ⁾(1) = (−1)ⁿ⁺¹ n! ζ(n+1), this second identity holds for the factorial 2! = 2, independently of the value of ζ(3).

For comparison, the next transformation on the page, x = −ξ/ε to the Laguerre equation, is correct up to renaming λ.

## Reproduce

```
python3 -I bochner733_check.py > bochner733_check.log
```

Standard library only.
