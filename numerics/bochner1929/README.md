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

## (B) The transformation of Normalform 2

Normalform 2 (p. 732) is y″ + (δ + εx)y′ + λy = 0. With ξ = a + bx and b = √(−ε/2), the coefficient of y_ξ after division by b² is −2ξ + (δ − εa/b)/b. The Hermite form needs this constant to vanish, i.e.

  ξ = −δ√(−1/(2ε)) + √(−ε/2)·x,  equivalently ξ = −(δ + εx)/√(−2ε).

The reflected choice ξ = (δ + εx)/√(−2ε) is equally valid; it changes Hₙ by (−1)ⁿ. Bochner prints

  ξ = δ√(−1/(2ε)) + √(−ε/2)·x,

with both terms of the same sign. That choice leaves y_ξξ − 2(ξ − 2a)y_ξ + λ′y = 0, which is not the Hermite form unless δ = 0. The script checks this on exact rational instances (ε = −2k², k = 1, 2, 3).

For comparison, the next transformation on the page, x = −ξ/ε to the Laguerre equation, is correct up to renaming λ.

## Reproduce

```
python3 -I bochner733_check.py > bochner733_check.log
```

Standard library only.
