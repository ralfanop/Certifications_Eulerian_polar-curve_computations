# Bo Peng's scheme (arXiv:2609.20074v1): independent check of the coefficient head

B. Peng, *A computer-assisted upper bound of 1.7813 for the real Grothendieck constant* (arXiv:2609.20074v1, 17 Sep 2026), proves K_G ≤ 1.7813 = π/(2γ), with γ = 5000π/17813.

**The scheme.**
- Rounding functions: f(w,x) = sgn(w + P(x)) and g(w,x) = f(w,−x).
- Threshold: P = Σ_{j∈{1,…,11} odd} α_j h_j, where h_j = He_j/√(j!).
- Correlations: corr(W,W′) = ρ(t) = Σ_{j≤51, j odd} c_j t^j and corr(X,X′) = t.
- The 6 + 26 exact decimals are copied verbatim from his Appendix A into `threshold_P.txt` and `rho.txt`.

The transcription of ρ is confirmed exactly: the program reproduces his (7), ‖ρ‖_A = 0.99997620388569307924355896.

**His criterion.** Lemma 2.2 requires γ + Σ_{n≥3}|b_n| < b₁. His Lemma 5.1 gives:
- b₁ > 0.881850816;
- Σ_{3≤n≤301}|b_n| < 3.0·10⁻⁸ (printed as 2.916517·10⁻⁸);
- B₃ < 107, so the tail is Σ_{n>301}|b_n| < 2.1527·10⁻⁵.

**Method.** The same two programs as for the cubic–quintic scheme (`../cubicquintic`).
- `alpha.c` (with the `he:` profile) encloses α_{m,n} for m + n ≤ 301 in Arb ball arithmetic. The threshold becomes a(u) = −(1/√2) Σ α_j ψ_j(u).
- `penghead.c` assembles H(t) = (π/2) Σ (−1)^m α_{m,n}² t^m ρ(t)^n and extracts b_k for k ≤ 301.

## Result (`out/penghead_301.log`)

| quantity | this check | Peng, (17)–(18) and (22) |
|---|---|---|
| b₁ | 0.881850816423338379 ± 9.7·10⁻¹⁹ | 0.88185081642333837919…, > 0.881850816 |
| Σ_{3≤n≤301, n odd} \|b_n\| | ≤ 2.91651651841·10⁻⁸ | < 2.916517·10⁻⁸ |
| b₁ − γ − head | 2.49708348326·10⁻⁵ | room for the tail |

**Agreement.** Both certified inputs agree to every printed digit.

**What remains.** The tail Σ_{n>301}|b_n| must stay below 2.4971·10⁻⁵. His bound is 2.1527·10⁻⁵, so the margin of his proof is 3.44·10⁻⁶, as he states. The independent tail bound is not yet done.

## Reproduce

```
../cubicquintic/alpha he:threshold_P.txt 301 256 out/alpha_peng_301.txt 45     # ~24 s
gcc -O2 -I$FLINT/include penghead.c -o penghead -L$FLINT/lib -lflint -lmpfr -lgmp -lm
./penghead out/alpha_peng_301.txt 301 256 rho.txt > out/penghead_301.log
```
