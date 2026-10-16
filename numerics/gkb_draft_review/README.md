# Review of the draft "On Grothendieck constants, type B Catalan numbers, and Fourier series" (August 2026)

This folder holds numerical checks made for an adversarial review of the draft. The checks use mpmath at 80 digits; the Euler–Kronecker check (`ek.py`) uses 40. They are evidence, not proofs. Appendix D (Davie) is excluded from the review.

| File | Content |
|---|---|
| `checks.py`, `checks.log` | Checks of the identities, grouped by outcome below. |
| `ek.py`, `ek.log` | γ_{Q(√2)} = γ + L′(1,χ₈)/L(1,χ₈) ≈ 1.2093306309411, which agrees with (C.6) to the precision of the numerical derivative (about 12 digits). It also prints log(2πe^γ) and 2 + √(8πγ) as reference values. |

**Identities in `checks.py` that hold**
- L(1,χ₈) = log(1+√2)/√2 and L(1,χ₋₈) = π/√8.
- Krivine's bound K_R equals L(1,χ₋₈)/L(1,χ₈).
- S₀ = Σ(−4)ⁿ/((2n+1)²C(2n,n)) = π²/8 − ½log²(1+√2), which also equals the digamma product (Lemma 2.15).
- Equations (2.73) and (2.143).
- Lehmer's sum (2.234).
- The Stieltjes combination equals 4√2π² (2.27).
- γ₁(1/8) ≈ −16.6417197636 (Example 2.5).

**Statements in `checks.py` that fail**
- Theorem 2.31: the left side is −σ₀, not σ₀.
- (2.141): ∫(1−erf²) equals √(8/π), not 8/π.
- (2.199): the Finch–Borwein constant is 0.88254, not 0.88524.
- Lemma 2.42: L₅(1)/log φ = 2/√5, not √5/2.
- (A.4): √2·√L₈(2) ≈ 1.3209, not π/√8.
- (1.5): the stated "minimal polynomial" x² − 2x + ½ has roots 1 ± 1/√2, not σ₀, and σ₀ is transcendental.

**Heilman's ε₀**
- K_R − π/(2(log(1+√2)+δ₀)) = πδ₀/(2L(L+δ₀)) ≈ 8.23·10⁻⁴⁵⁷.
- This is a **lower** bound for K_R − K_G (the improvement over Krivine), not an upper bound on the gap.

## Reproduce

```
python3 -I checks.py > checks.log   # needs mpmath
python3 -I ek.py > ek.log
```
