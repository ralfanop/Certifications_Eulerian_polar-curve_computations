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

---

## Rendiconti version V017 (29 October 2026): `kkd_arb_v017.c`, `kkd_arb_v017.log`, `kkd_arb_rerun.diff`

Paper: R. Alfano, *Explicit identities connecting Krivine's Grothendieck bound, König's bilinear form, and quadratic Dirichlet L-series*, Rendiconti di Matematica e delle sue Applicazioni typeset version V017. Equation numbers are those of V017, (1)–(91). The decimal checks are those of `kkd_arb.c`, unchanged except for the equation labels; the identity checks are new.

**Equation concordance, TJM → V017, for the certified decimals:** (6)→(9), (9)→(12), (11),(82)→(14),(85), (25)→(28), (27)→(30), (29)→(32), (31)→(34), (33)→(36), (39)→(42), (40)→(43), (64)→(67), (65)→(68), (66)→(2),(69), (83)→(86), (84)→(87), (85)→(88), (86)→(89), (88)→(91).

**Correction to the table above:** the decimal expansion of γ₈ printed in (40) of the TJM version and (43) of V017 has **74** decimals, not 75; the program counts the decimals from the printed string and certifies all 74 as correctly rounded.

All 17 decimals are certified as correctly rounded in `kkd_arb_v017.log`; `kkd_arb_rerun.diff` records that the CI re-run of `kkd_arb.c` reproduces `kkd_arb.log` identically.

**Identity checks (left side minus right side; each enclosure must contain 0).** Corollary 3.5, (24)–(27), with the V017 corrections of (33) [M₀ in place of I₁] and (35) [√𝒫_A I₁ in place of 𝒫_A I₁]; the two V016 forms are also evaluated and are nonzero (−0.18943776… and 0.59776608…). All other enclosures are of radius below 10⁻³⁰⁵ and contain 0. Further: (17) L₋₈(1)/L₈(1) = K_G^ℝ with L₋₈(1) from the Hurwitz zeta function; (19); Coffey's identity (37) and Theorem 3.11, (55), through ζ(2,a) = 1 + Σ_k (−1)^k γ_k(a)/k!, i.e. the Laurent expansion (4) at s = 2; (61)–(63) for arctan(i/√2); (66)–(69) for ₂F₁(1/2,1/2;3/2;±1); (70); (81)–(82).

These enclosures are certified numerical agreement, not proofs; the proofs are in the paper.

**Not certified here:** the ₃F₂ evaluations (76)–(77), quoted from Krupnikov and Kölbig; the integral in (90), quoted from Finch; values quoted from the literature (κ ≈ 1.6770; the bounds claimed in arXiv:2610.10477).

## Reproduce (V017)

```
gcc -O2 -I$FLINT/include kkd_arb_v017.c -o kkd_arb_v017 -L$FLINT/lib -Wl,-rpath,$FLINT/lib -lflint -lmpfr -lgmp -lm
./kkd_arb_v017 1024 > kkd_arb_v017.log
```

The workflow `.github/workflows/kkd-v017-cert.yml` builds FLINT 3.3.1 from the official release, re-runs `kkd_arb.c` (its output must equal `kkd_arb.log`) and runs `kkd_arb_v017.c`.
