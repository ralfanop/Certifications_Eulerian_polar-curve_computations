# Heilman's proof, Appendix A: exact certification and the role of 231

This folder certifies the numerical chain (A.14)–(A.80) of Appendix A (Heilman's proof) in the draft *A second look at Braverman et al.'s Theorem*. It also settles one question: is the constant 231 = 2n + 1 intrinsic to the proof, or only the optimum of the choices made in it?

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
| `lean_mirror.py` | Re-evaluates with `Fraction` every statement of `lean/Heilman/AppendixA231.lean` |

The Lean 4 counterpart is `lean/Heilman/AppendixA231.lean`. It uses core Lean only: no Mathlib, no `native_decide`. Every theorem is a rational inequality checked by the kernel.

## Result on 231

- With the certified ρ = 1.152, M_φ = 155.0302861362, L = 34.1627465436, Δ ≥ 4.29244734953e-21 and ε = 0.664 Δ/L, the least n with tail(n) < ε/2 is **n = 115**, so 2n + 1 = 231. Here q = 0.9/ρ = 25/32 exactly.
- **n = 114 is impossible for every admissible ε**:
  - δ₀ > 0 requires ε < Δ/L;
  - tail(114) = 6.8271e-23 ≥ Δ/(2L) = 6.2823e-23.
- **232 and 233 give valid proofs.** Sign control holds strictly for k = 0..115, δ₀ > 0, and p < p₀.₉₂, p₀.₉₆. The bounds on K_Kr − K_G are weaker:

  | m | δ₀ ≥ | K_Kr − K_G ≥ |
  |---|---|---|
  | 232 | 2.0215e-459 | 4.0878e-459 |
  | 233 | 9.9950e-462 | 2.0210e-461 |

  The same holds for 234, 235, 241 and 301.
- 230 violates sign control at k = 115.
- The value 231 depends on the free factor c in ε = cΔ/L:

  | c | 2n + 1 |
  |---|---|
  | 0.1 | 239 |
  | 0.3 | 235 |
  | 0.5 | 233 |
  | 0.664 to 0.99 | 231 |

So 231 is the extremum of the choices made, not an intrinsic constant.

## Printed slips (the 6 FAIL lines of the log)

None of these affects the conclusion. After outward rounding, (A.79) K_Kr − K_G ≥ 8.23e-457 still holds.

- **(A.39)** p₀.₉₂ = 1.205084539442e-4 is below the printed lower bound 1.20508454e-4.
- **(A.45)–(A.46)** 12 × 381.8015394237 = 4581.6184730844 exceeds the printed M = 4581.618473084.
- **(A.47)** √((6/7)² + 7²) = 7.0522828841128… exceeds the printed 7.05228288411.
- **(A.49)** The printed value 2.01664948e18 is that of 2C_r/r·(0.9/r)·[1 − (0.9/r)²]⁻¹. The printed formula 2C_r/r·(0.9/r)·[1 − 0.9/r]⁻² gives 1.835e20 instead. Either way the C′p² term is negligible.
- **(A.63)** At k = 115 with p = p(231), sign control holds with equality at the level of the bounds. Strictness requires sup|φ| < M_φ strictly on |z| = ρ.
- **(A.66)** The exact δ₀ = 4.07123102830199e-457 is below the printed 4.07123102832e-457. Eleven digits survive: 4.0712310283e-457.

## Reproduce

```
python3 ri.py                    # self-test
python3 appendixA_chain.py       # 35/41; the 6 FAILs are the printed slips above
python3 lean_mirror.py           # 28/28
lean ../../lean/Heilman/AppendixA231.lean   # any Lean 4 toolchain with `decide +kernel`
```
