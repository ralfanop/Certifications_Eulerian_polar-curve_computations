# j-invariant at the CM points of the Gauss–Heegner numbers

Status: **certified by us** (Arb ball arithmetic, 256 bits, together with exact integer arithmetic; 15 Oct 2026). Files: `heegner_j.c`, `heegner_j.log`.

For each H in {1, 2, 3, 7, 11, 19, 43, 67, 163} we take the CM point τ = i√H for H = 1, 2 and τ = (1 + i√H)/2 otherwise. Because the class number is 1, the theory of complex multiplication makes j(τ) a rational integer. The program encloses j(τ) in a ball of radius < 1/2 that contains exactly one integer, and checks that this integer is the stated one.

| H | j(τ) |
|---|---|
| 1 | 1728 |
| 2 | 8000 |
| 3 | 0 |
| 7 | −3375 |
| 11 | −32768 |
| 19 | −884736 |
| 43 | −884736000 |
| 67 | −147197952000 |
| 163 | −262537412640768000 |

## Exact checks related to Kontsevich–Zagier, p. 797 (`../kz797/`)

- N(27 + 19√2) = 27² − 2·19² = 7. Hence (27 + 19√2)/(27 − 19√2) = (27 + 19√2)²/7 = (1451 + 1026√2)/7.
- j(i) − j(i√2) = 1728 − 8000 = −6272 = −2⁷·7², so 7² divides it.

By the Gross–Zagier theorem on singular moduli (J. reine angew. Math. 355, 1985), the primes dividing j(τ₁) − j(τ₂) for discriminants −d₁ and −d₂ are at most d₁d₂/4. Here d₁ = 4 and d₂ = 8, so only 2, 3, 5 and 7 are possible, and indeed 2 and 7 occur. The prime 7 in the norm of 27 + 19√2 is the same prime 7 that divides j(i) − j(i√2). We have checked the agreement of the primes; we have not verified a causal link between the two occurrences of 7.

The numbers that appear on the right-hand side of the identity are 1, 2, 3 (27 = 3³), 7 (the norm) and 19. All of them are Gauss–Heegner numbers.

## Reproduce

```
gcc -O2 -I$FLINT/include heegner_j.c -o heegner_j -L$FLINT/lib -Wl,-rpath,$FLINT/lib -lflint -lmpfr -lgmp -lm
./heegner_j > heegner_j.log
```
