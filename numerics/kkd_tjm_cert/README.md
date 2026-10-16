# Krivine–König–Dirichlet identities (TJM version): certified decimals

Paper: R. Alfano, *Explicit identities connecting Krivine's Grothendieck bound, König's bilinear form, and quadratic Dirichlet L-series*, TJM version of 16 October 2026. Equation numbers are those of that version, (1)–(88).

## What is certified (`kkd_arb.log`)

The computation uses Arb ball arithmetic (FLINT 3.3.1) at 1024 bits. A displayed decimal is certified when a rigorous enclosure of the exact quantity lies inside the rounding cell of that decimal.

**Every decimal derived in the paper is certified as correctly rounded (17 checks):**

| Eq. | Quantity | Value |
|---|---|---|
| (6) | I₁ = √8 log(1+√2) | 2.49290 |
| (9) | 2 log(1+√2)/π | 0.561100 |
| (11), (82) | M₀ = L₈(1) = log(1+√2)/√2 | 0.623225 |
| (25) | √2 log(1+√2)/(8π²) | 0.015786 |
| (27) | log(1+√2)/(√2 √(2π)) | 0.24863 |
| (29) | log(1+√2)/(√2 π²) | 0.0631459 |
| (31) | 2 log(1+√2)/√π | 0.99452 |
| (33) | γ₁(1/8), from `acb_dirichlet_stieltjes` | −16.64171976 |
| (40) | γ₈ = γ + L′(1,χ₈)/L(1,χ₈), 75 decimals | 1.20933063094138118664026424093547097334700909059315456011578210585217390057 |
| (64) | log(1+√2) | 0.88137 |
| (65) | π/2 | 1.57080 |
| (66) | K_R = π/(2 log(1+√2)) | 1.78221 |
| (83) | L₋₈(1) = π/√8 | 1.11072 |
| (84) | √(2π) | 2.50663 |
| (85) | 4π² | 39.47842 |
| (86) | P_A = 1/(2π) | 0.15915 |
| (88) | P_γ = arctan(1/2)/π | 0.14758 |

**Closed forms:**
- Blagouchine's closed form for γ₁(1/8), as printed in (33), minus Arb's γ₁(1/8): [± 3.6·10⁻³⁰⁶].
- (39), γ₈ = log(2πe^{2γ}) + (R(1/8) − R(3/8) − R(5/8) + R(7/8))/(2 log(1+√2)) with R(x) = −∂²ζ(s,x)/∂s² at s = 0, minus γ₈ from L′/L: [± 4.7·10⁻³⁰⁷].
- L₈(1) from the Hurwitz zeta function minus log(1+√2)/√2: [± 5.7·10⁻³⁰⁸].

These enclosures contain 0 and are tiny. That is certified numerical agreement, not a proof of the identities.

**Corrections found by this run (16 October 2026).** Four decimals in the paper were truncated, not rounded: (9) 0.561099, (65) 1.57079, (84) 2.50662 and (85) 39.47841. The paper now prints the rounded values 0.561100, 1.57080, 2.50663 and 39.47842. γ₈ is computed with the deflated Hurwitz zeta series at s = 1; L′(1)/L(1) = D′/D − log 8, with D(s) = Σ χ₈(a) ζ(s, a/8).

**Not certified here:** values quoted from the literature, namely the Davie–Reeds lower bound κ ≈ 1.6770, and the bounds 1.773 ≤ K_G ≤ 1.7799 and K_G ≈ 1.779, which Heilman, Jones and Malavolta claim in arXiv:2610.10477.

## Reproduce

```
gcc -O2 -I$FLINT/include kkd_arb.c -o kkd_arb -L$FLINT/lib -Wl,-rpath,$FLINT/lib -lflint -lmpfr -lgmp -lm
./kkd_arb 1024 > kkd_arb.log
```
