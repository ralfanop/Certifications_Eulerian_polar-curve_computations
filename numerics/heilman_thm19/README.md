# Heilman's Theorem 1.9: independent certification

S. Heilman, *An upper bound on Grothendieck's constant* (arXiv:2606.00247v1), Theorem 1.9, states that rigorous interval arithmetic gives

  K_G < π/(2 log(1+√2)) − 10⁻⁵.

The scheme is f_η(x) = sign(x₂ − η h₃(x₁)) and g_η(x) = sign(x₂ + η h₃(x₁)), with η = 0.04249900400783211 (Section 16), where h₃(t) = (2t³ − 3t)/(π^{1/4}√3). His certificate is a set of Sage programs (`rouche_v9.sage`, `groth_series_verify.sage`, `arb_h3_A09_certificate_panel.sage`). We have not run or checked them.

This folder certifies the statement **independently of his code**. It uses the pipeline of `../heilman3e5`:

- **Hermite coefficients.** `../cubicquintic/alpha` encloses α_{m,n} for m + n ≤ 200 in Arb, with the main region [0, 8].
- **Finite part and tail.** `../heilman3e5/certify` performs the series reversion and the Rouché tail. It uses s = 1.02 and ρ′ = 1.10, with the profile-independent bound sup_{|ζ|=1.10}|E(sin ζ)| ≤ 23.08 from `../heilman3e5/mbound.c`.
- **Closing step.** `closing.py` checks it in exact rationals, and `lean/Heilman/HeilmanThm19Closing.lean` in the Lean kernel: 20 theorems, no axioms, Lean 4.35.0.

The profiles are `profile_A.txt` (coefficient η for h₃) and `profile_B.txt` (coefficient −η), with η read as an exact decimal.

## Result (`out/certify.log`, `out/closing.log`)

| quantity | value |
|---|---|
| C₁ | 0.9980452537952252449823432 ± 2·10⁻²⁶ |
| b₁, b₃, b₅ | 1.0019585747212779408, −0.16508817892876219944, 0.0072481098105396004252 |
| A₂₀₀(γ_t), γ_t = π/(2(K_Kr − 10⁻⁵)) | 0.9999996472167305064236 ± 5·10⁻²⁴ |
| δ, R′ | ≤ 0.0051458, 1.0148541959 |
| tail Σ_{n>200}\|b_n\|γ_tⁿ | ≤ 4.50·10⁻¹² |
| **A(γ_t) − 1** | **≤ −3.5278·10⁻⁷**, hence **K_G ≤ K_Kr − 10⁻⁵** |
| best certified | K_G ≤ 1.782203471795465 = K_Kr − ε, ε ≥ 1.0506395904·10⁻⁵ |
| limit of this scheme | ε* < 1.0506420012·10⁻⁵ |

**Theorem 1.9 holds for Heilman's scheme, with strict inequality.** The scheme gives exactly K_Kr − ε* with 1.05063959·10⁻⁵ < ε* < 1.05064201·10⁻⁵.

## Reproduce

```
../cubicquintic/alpha profile_A.txt 200 256 out/alpha_A_200.txt 80
../cubicquintic/alpha profile_B.txt 200 256 out/alpha_B_200.txt 80
../heilman3e5/certify out/alpha_A_200.txt out/alpha_B_200.txt 200 256 200 1.02 1.10 23.1 1e-5 out/bounds.txt > out/certify.log
python3 closing.py --lean ../../lean/Heilman/HeilmanThm19Closing.lean > out/closing.log
lean ../../lean/Heilman/HeilmanThm19Closing.lean
```
