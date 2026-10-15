# Hermite polynomials, type-B Catalan numbers C(2k,k), and Grothendieck's constant over ℝ and ℂ

Status: **certified by us** (15 Oct 2026). The identities are classical; what we certify are the exact coefficient identities and the numerical agreements listed below.

| File | What it checks | Method |
|---|---|---|
| `exact_checks.py`, `exact_checks.log` | (A), (B), (C) | exact integers and rationals, standard library only |
| `series_arb.c`, `series_arb.log` | (D), (E) | Arb ball arithmetic (FLINT 3.3.1) |

## (A) Type-B Catalan numbers are Hermite values at 0

H₂ₙ(0) = (−1)ⁿ C(2n,n) n!, for the physicists' Hermite polynomials. This follows from the recurrence H_{n+1}(0) = −2n H_{n−1}(0) and is verified exactly for n ≤ 200.

## (B) They are the squared Hermite coefficients of sign(x)

Let X ~ N(0,1), let Heₙ be the probabilists' Hermite polynomials, and let cₙ = E[sign(X) Heₙ(X)]/√(n!). Since d/dx[He_{n−1}φ] = −Heₙφ, where φ is the N(0,1) density, we get E[sign X · He_{2k+1}(X)] = 2φ(0)He_{2k}(0). Therefore

  c²_{2k+1} = (2/π) ((2k−1)!!)²/(2k+1)! = (2/π) C(2k,k)/(4ᵏ(2k+1)),  c_{2k} = 0.

The second equality is verified exactly for k ≤ 200. Grothendieck's identity E[sign X sign Y] = (2/π) arcsin ρ is then the series Σ c²ₙ ρⁿ in type-B Catalan numbers, and Parseval (Σ c²ₙ = 1) gives Σ C(2k,k)/(4ᵏ(2k+1)) = π/2.

## (C) Haagerup's function for the complex constant

From the Wallis integral ∫₀^{π/2} cos²s sin^{2k}s ds = (π/2) C(2k,k)/(4ᵏ(2k+2)), verified exactly for k ≤ 200, we get

  φ_ℂ(t) = t ∫₀^{π/2} cos²s (1 − t² sin²s)^{−1/2} ds = (π/4) Σ_{k≥0} C(2k,k) C_k t^{2k+1}/16ᵏ,  with C_k = C(2k,k)/(k+1).

The type-A Catalan numbers C_k and the type-B Catalan numbers C(2k,k) appear together. φ_ℂ is the function in Haagerup's bound for K_G^ℂ (Israel J. Math. 60, 1987).

## (D) Krivine's constant as a type-B Catalan series

  log(1 + √2) = arcsinh 1 = Σ_{k≥0} (−1)ᵏ C(2k,k)/(4ᵏ(2k+1)),  so  π/(2 log(1 + √2)) = 1.78221397819136911177441345297…

Arb certifies this for N = 2²² terms with the alternating-series tail bound: the enclosure is 0.8813735870 ± 3.6·10⁻¹¹, and it contains log(1 + √2). The series converges slowly, because its terms decay like k^{−3/2}. It is used here as an identity, not as a means of computation.

## (E) Haagerup series against integral

At t = 1/2, 9/10 and 99/100, the integral (certified by `acb_calc_integrate`) and the series (with the geometric tail bound a_K t²/(1 − t²)) agree to 40 digits; the balls overlap. Run time 1.6 s.

## Reproduce

```
python3 -I exact_checks.py > exact_checks.log
gcc -O2 -I$FLINT/include series_arb.c -o series_arb -L$FLINT/lib -Wl,-rpath,$FLINT/lib -lflint -lmpfr -lgmp -lm
./series_arb > series_arb.log
```
