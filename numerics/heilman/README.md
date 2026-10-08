# Heilman's proof, Appendix A: exact certification and the role of 231

This folder certifies the numerical chain (A.14)–(A.80) of Appendix A (Heilman's proof) in the draft *A second look at Braverman et al.'s Theorem*. It also settles one question: is the number 231 = 2n + 1 intrinsic to the proof, or the optimum of the choices made in it? Section 3 of the draft presents these results. This folder holds the code and the full data tables that are too long for the manuscript.

All arithmetic is exact. `ri.py` implements interval arithmetic with Python `Fraction` endpoints, using:
- π from Machin's formula;
- √2 by integer square root;
- log(1+√2) = 2·artanh(√2 − 1).

Each is enclosed at scale 10^800, with every rounding taken outward. No floating point enters any check.

| File | Content |
|---|---|
| `ri.py` | Exact rational interval arithmetic (self-test included) |
| `appendixA_chain.py` | Part I: the chain (A.14)–(A.80). Part I-bis: the chain re-run with every bound rounded outward. Part II: the role of 231 |
| `appendixA_chain.log` | Output of `python3 appendixA_chain.py` |
| `generate_data.py` | Writes the tables in `data/` |
| `lean_mirror.py` | Re-evaluates with `Fraction` every statement of `lean/Heilman/AppendixA231.lean` |

The Lean 4 counterpart is `lean/Heilman/AppendixA231.lean`. It uses core Lean only: no Mathlib, no `native_decide`. Every theorem is a rational inequality checked by the kernel.

## Result on 231

The certified constants are:
- ρ = 1.152, so q = 0.9/ρ = 25/32 exactly;
- M_φ = 155.0302861362;
- L = 34.1627465436;
- Δ ∈ [4.29244734953296e-21, 4.29244734953300e-21].

Write ε = cΔ/L. Note that δ₀ = p(Δ − Lε) − LC′p² > 0 forces c < 1.

- **The tail condition is a threshold in c.** tail(n) < ε/2 if and only if c > c(n) := 2L·tail(n)/Δ, and c(n) = c(115)·q^{2(n−115)}. The thresholds are:

  | n | c(n) |
  |---|---|
  | 114 | 1.0867… |
  | 115 | 0.663282408722… |
  | 116 | 0.4048… |

- **n = 114 is impossible for every admissible ε**, because c(114) > 1. Hence n ≥ 115.
- **Heilman's c = 0.664 is c(115) rounded up at the third decimal.** It is the smallest three-digit c for which n = 115 works.
- **Sign control.** R(m,k) := p(m)·M_φ·ρ^{−(2k+1)}·2(2k+1)! = ρ^{m−2k−1}(2k+1)!/m! increases in k, so k = n is the binding index.
  - R(m,n) > 1 for m ≤ 2n.
  - R(2n+1,n) = 1, which is the equality case of (A.63).
  - R(m,n) < 1 for m ≥ 2n+2. In particular R(232,115) = ρ/232 and R(233,115) = ρ²/(232·233).
- **Every m ≥ 232 gives a valid proof** (δ₀ > 0 and p(m) < p₀.₉₂, p₀.₉₆), with weaker bounds:

  | m | δ₀ ≥ | K_Kr − K_G ≥ |
  |---|---|---|
  | 232 | 2.0215e-459 | 4.0878e-459 |
  | 233 | 9.9950e-462 | 2.0210e-461 |

  Further rows are in `data/delta0_vs_m.csv`.
- **231 is the unique maximiser of the certified gap.**
  - For any m ≥ 232, δ₀ < p(232)Δ < 6.02e-459.
  - For m = 231, sup over ε of δ₀ = p(231)(Δ − 2L·tail(115)) − LC′p(231)² ∈ [4.07992590889e-457, 4.07992590890e-457].
  - Heilman's ε reaches at least 99.78% of that supremum.
- **231 is optimal for these constants, but not intrinsic to the method.** n_min = ⌈n*⌉ with n* = ½[log_{1/q}(2LM_φ/((1−q²)cΔ)) − 3].
  - Every gain by a factor q⁻² = 1.6384 in Δ/(LM_φ) lowers n by 1, and so m by 2.
  - A tenfold gain lowers n by ≈ 4.66.
  - Changing ρ changes q and M_φ.

## Data tables (`data/`)

| File | Content |
|---|---|
| `tail_vs_n.csv` | n = 100..130: tail(n) and the enclosure [c(n)_lo, c(n)_hi] |
| `sign_control_ratios.csv` | R(m,k) for k = 0..115 and m = 229..241 |
| `sign_control_at_k115.csv` | R(m,115) and the verdict for m = 229..241 |
| `delta0_vs_m.csv` | m = 231..260, 281, 301, 351, 401: p(m), δ₀ and K_Kr − K_G, with Heilman's ε and with the optimal ε |
| `nmin_vs_c.csv` | c = 0.01..0.99, plus 0.66328, 0.66329 and 0.664: n_min, m = 2n_min + 1, δ₀, gap |
| `printed_slips.csv` | The six printed values of Appendix A against the exact values |

Decimals in columns named `_lo` are rounded down and those named `_hi` are rounded up. Other columns are rounded to nearest.

## Printed slips (the 6 FAIL lines of the log)

None of these affects the conclusion. After outward rounding, (A.79) K_Kr − K_G ≥ 8.23e-457 still holds.

- **(A.39)** p₀.₉₂ = 1.205084539442e-4 is below the printed lower bound 1.20508454e-4.
- **(A.45)–(A.46)** 12 × 381.8015394237 = 4581.6184730844 exceeds the printed M = 4581.618473084.
- **(A.47)** √((6/7)² + 7²) = 7.0522828841128… exceeds the printed 7.05228288411.
- **(A.49)** The printed value 2.01664948e18 is that of 2C_r/r·(0.9/r)·[1 − (0.9/r)²]⁻¹. The printed formula 2C_r/r·(0.9/r)·[1 − 0.9/r]⁻² gives 1.835e20 instead. Either way the C′p² term is negligible; all checks here use C′ ≤ 1.84e20.
- **(A.63)** At k = 115 with p = p(231), sign control holds with equality at the level of the bounds. Strictness requires sup|φ| < M_φ strictly on |z| = ρ.
- **(A.66)** The exact δ₀ = 4.07123102830199e-457 is below the printed 4.07123102832e-457. Eleven digits survive: 4.0712310283e-457.

## Reproduce

```
python3 ri.py                    # self-test
python3 appendixA_chain.py       # 35/41: 29 printed steps (23 pass, 6 slips) + 12 further checks
python3 generate_data.py         # writes data/*.csv
python3 lean_mirror.py           # 34/34
lean ../../lean/Heilman/AppendixA231.lean   # any Lean 4 toolchain with `decide +kernel`
```

## Lean status

`lean/Heilman/AppendixA231.lean` compiles with **Lean 4.22.0**, built from source, in about 2 s. The compiler output is in `lean/Heilman/AppendixA231.log`.

- 33 theorems are certified.
- 32 of them are kernel computations (`decide +kernel`) and depend on **no axioms**.
- `n114_impossible` is a short proof by hand. It uses only the three standard Lean axioms.
- Two auxiliary order lemmas (`Q.lt_trans`, `Q.not_lt_of_le`) support `n114_impossible`.
- The negations of two natural but false variants are theorems of the file: `sign_230_fails` (sign control for m = 230 at k = 115) and `tail_114` (tail(114) < ε/2 fails).
- `lean_mirror.py` re-evaluates the 32 decided theorems in 34 checks.
