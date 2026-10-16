# V291, Block B: numerical checks for the adversarial review

These checks support the adversarial review of Block B of the V291 draft (Sections 3, 4.8–4.10, 6.1–6.4 and Appendix A; Remark 4.11 is excluded). They are numerical evidence, not proofs. Precision is 40 digits for the identities, and double precision with sparse LU for the determinants.

| File | What it checks |
|---|---|
| `identities.py`, `identities.log` | Dirichlet's cotangent class-number formula for p = 7, 11, 19, 23, 31, 43, 47, 67, 163, compared with h(−p) = −(1/p)Σ k(k/p). Also checks:<br>• arctan(i/√2) = i log(1+√2);<br>• Khrushchev's continued fraction (E.31), evaluated backwards to depth 10⁴ (it converges like depth^(−1/2));<br>• Σ(−1)^(n−1)/(n C(2n,n)) = (2/√5) log φ;<br>• 2⁴⁷−1 = 2351·4513·13264529;<br>• the zero set of Ẑ_cyc;<br>• 2u⁴−4u²+1 = T₄(u/√2) at u = √(1−1/√2);<br>• the Fagnano abscissa of the lemniscate arc bisection;<br>• (1+√2)⁴ = 17+12√2;<br>• Σ C(2n,n)² z²ⁿ = ₂F₁(½,½;1;16z²). |
| `square_loop_rate.py`, `square_loop_rate.log` | The last-erased-loop fraction F_L of the L×L square on Z², computed as 4^(−4L) det(I−A/4)_{B∖p} / det(I−A/4)_{B∖v}. B is the (4L+1)² box with a Dirichlet boundary, p is the 4L boundary vertices of the square and v is one vertex of p. The discrete slope of log F_L in L tends to 4 log(√2−1) = −3.52549; it is −3.5325 at L = 64, with a drift of the size an O(log L) term gives. |

## Findings these runs support

1. **The cotangent formula is correct.** It gives h(−p) for every prime tested (1, 1, 1, 3, 3, 1, 5, 1, 1).
2. **The appendix identities are correct.** Every identity of Appendix A that was tested holds. However, 2u⁴−4u²+1 is not a reciprocal (palindromic) polynomial, so calling it a "reciprocal quartic" is wrong.
3. **The leading decay rate is numerically consistent.** The rate (√2−1)^{4L} of the large-square fraction matches the numbers, and it is what Kenyon's perimeter term predicts: (log(√2−1)/2) per boundary vertex, counted on both sides of the polygon. The reference is R. Kenyon, *The asymptotic determinant of the discrete Laplacian*, Acta Math. 185 (2000) 239–286, arXiv:math-ph/0011042. The √2−1 comes from the square-lattice Laplacian at its extreme Fourier mode, where 4−2cos π = 6 has the root 3+2√2 = (1+√2)². It is not a cyclohedral quantity.
4. **The "Leonardo" sequence is an error record.** OEIS A221180 is titled "Erroneous version of A000079" and carries the keyword *dead*. It records Leonardo da Vinci's slip 8092 for 8192 (Codex Madrid I, f. 75r; Huylebrouck, Math. Intelligencer 34(4) 2012). This has two consequences:
   - The factor 2023 = 8092/4 and everything derived from it are the arithmetic of a copying error.
   - The count 36 is simply the number of terms listed in the OEIS entry.

## Reproduce

```
python3 -I identities.py > identities.log        # needs mpmath
python3 -I square_loop_rate.py > square_loop_rate.log   # numpy + scipy, about 2 s
```
