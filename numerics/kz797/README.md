# Kontsevich–Zagier, *Periods* (2001), p. 797: 1000 certified digits

Source: M. Kontsevich, D. Zagier, *Periods*, in B. Engquist, W. Schmid (eds.), *Mathematics Unlimited — 2001 and Beyond*, Springer 2001, pp. 771–808. The identity is on p. 797. It concerns the higher Green's function of weight 4 for the full modular group at the CM points i and i√2, that is d = 1 and d = 2, the first two Gauss–Heegner numbers:

  20G/π + 1728π² ∫_{√2}^∞ E₄(iy)Δ(iy)/E₆(iy)² · (y² − 2) dy  ≟  log((27 + 19√2)/(27 − 19√2)).

G is Catalan's constant. According to the authors, the left-hand side is the provable value of −G₂(i, i√2)/√2 and the right-hand side the predicted value. In the paper the identity is stated as **conjectural** (≟).

Status: **numerically certified by us to 1000 digits** (15 Oct 2026). This is a certified numerical agreement, not a proof of the identity. A proof of this case may exist in the later literature (possibly A. Mellit's 2008 Bonn thesis on higher Green's functions); we have not checked it.

## Result (`kz797_1000.log`)

- Precision 3410 bits; the integral is taken on [√2, 387] and the tail is bounded analytically.
- Both sides agree: |LHS − RHS| ≤ 3.84·10⁻¹⁰²⁴ < 10⁻¹⁰⁰⁰.
- Value: LHS = RHS = 6.02723946596899677985500120455788713524416586107838160…; all 1000 digits are in the log.
- Run time 6 s.

## G recomputed from the identity (`kz797_1000.log`, `kz797_3000.log`)

Solving the identity for Catalan's constant gives

  G_KZ = (π/20) · ( log((27 + 19√2)/(27 − 19√2)) − 1728π² ∫_{√2}^∞ E₄(iy)Δ(iy)/E₆(iy)² · (y² − 2) dy ).

We computed G_KZ independently of any Catalan routine and extracted its exact (truncated) decimals. We then compared them digit by digit with G from `arb_const_catalan` (see also `../catalan/`).

- 1000 digits: all 1000 decimals of G_KZ agree with G, and |G_KZ − G| ≤ 6.1·10⁻¹⁰²⁵ (5 s).
- 3000 digits: all 3000 decimals agree, and |G_KZ − G| ≤ 1.9·10⁻³⁰²⁸ (76 s; tail bound 1.0·10⁻³⁰⁵⁰).

Up to 3000 digits, the identity shows no deviation.

## Method

The computation uses Arb ball arithmetic (FLINT 3.3.1).

- E₄ = G₄/(2ζ(4)) and E₆ = G₆/(2ζ(6)) come from `acb_modular_eisenstein`, and Δ from `acb_modular_delta`, all at τ = iy.
- `acb_calc_integrate` computes the integral over [√2, Y] with certified error bounds, on dyadic subintervals. The integrand is meromorphic. Whenever a complex ball meets a zero of E₆ or leaves Re y > 0, its evaluation returns a non-finite value, as the integrator requires.
- The tail over [Y, ∞) is added as an error radius. For y ≥ Y = 387, q = e^{−2πy} < 10⁻¹⁰⁰⁰. Hence |E₄ − 1| ≤ 240 Σ n⁴qⁿ < 1, |E₆ − 1| ≤ 504 Σ n⁶qⁿ < 1/2, and 0 < Δ = q ∏(1 − qⁿ)²⁴ ≤ q. So |integrand| ≤ 8y²e^{−2πy} and

  tail ≤ 8e^{−aY}(Y²/a + 2Y/a² + 2/a³),  with a = 2π,

  which is 1.79·10⁻¹⁰⁵¹.

## Reproduce

```
gcc -O2 -I$FLINT/include kz797_arb.c -o kz797_arb -L$FLINT/lib -Wl,-rpath,$FLINT/lib -lflint -lmpfr -lgmp -lm
./kz797_arb 1000 > kz797_1000.log
./kz797_arb 3000 > kz797_3000.log
```
