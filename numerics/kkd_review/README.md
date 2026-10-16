# Review of "Explicit identities connecting Krivine's sharp Grothendieck bound, König's bilinear form, and quadratic Dirichlet L-series" (Filomat submission, print of October 2026)

These are numerical checks for an adversarial review, made with mpmath. They are evidence, not proofs.

| File | What it checks |
|---|---|
| `kkd_checks.py`, `kkd_checks.log` | See the list below. |
| `n_growth.py`, `n_growth.log` | The right-hand side of (4) as printed, for n = 1, 2, 5, 10, 100, 1000: 0.886, 1.43, 2.53, 3.75, 12.5, 39.8. It grows like √n, so it cannot tend to Krivine's bound as stated. |

`kkd_checks.py` checks the following:

1. **Bilinear form, (5)–(7) and (14).** The kernel integral over the quadrant (0,∞)² with f = g = 1 equals log(1+√2)/√2 = M₀. Over the whole plane with f = g = sign it equals 4M₀ = √8 log(1+√2) = I₁. As printed, (5) and (6) integrate over (0,∞)², where sign ≡ 1, so (6) equals M₀ and not I₁.
2. **Equation (43).** It holds with Deninger's R(x) = −∂²ζ(s,x)/∂s² at s = 0: the value agrees with (44) to about 13 digits, the accuracy of the numerical differentiation.
3. **Table 1.** H₂ = 3/2, not 2/3.
4. **Equation (93).** ∫(1−erf²) = √(8/π), so 16P_A/∫(1−erf²) = √(8/π) ≈ 1.596, not 1. By contrast, c_R = ½∫(1−erf²) = √(2/π) is correct.
5. **Equations (38), (40) and (57).** They are correct: Coffey's combination equals the Hurwitz combination ζ(2,1/8) − ζ(2,3/8) − ζ(2,5/8) + ζ(2,7/8) = √32 π².
6. **Equations (12)–(13).** πδ₀/(2L(L+δ₀)) ≈ 8.23·10⁻⁴⁵⁷ is K_R − π/(2(L+δ₀)), that is, a lower bound for K_R − K_G. As printed, (12) gives this gap as an upper bound for K_G.

## Reproduce

```
python3 -I kkd_checks.py > kkd_checks.log
python3 -I n_growth.py > n_growth.log
```

## Correction (16 October 2026)

An earlier version of this review said that (86) was wrong by a factor 2 and that "fundamental unit of norm 1" was wrong. Both statements were mistaken. In Edwards, *Fermat's Last Theorem* (1977), §9.3, p. 349, D is the squarefree *determinant*, and E is the fundamental unit **with norm 1**: E = ε if N(ε) = 1, and E = ε² if N(ε) = −1.

For D = 2 this gives ε = 1+√2, which has norm −1, so E = (1+√2)² = 3+2√2. Then log E/(2√2) = log(1+√2)/√2, and (86) is correct. Likewise (88) is Edwards' formula for D < 0 on p. 346, with h = 1; it is correct.

Two terminology points remain. In the paper, "fundamental discriminant D = ±2" should read "squarefree determinant D = ±2, in Edwards' convention". For D = −2, the phrase "fundamental unit E of norm 1" has no role, because no unit enters the formula when D < 0.
