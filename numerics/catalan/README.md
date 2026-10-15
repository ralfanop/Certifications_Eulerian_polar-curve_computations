# Catalan's constant G: 1000 exact decimals

G = Σ_{n≥0} (−1)ⁿ/(2n+1)² = 0.9159655941 7721901505 4603514932 …

Status: **certified by us** (15 Oct 2026). The 1000 decimals listed in `catalan_1000.log` are exact, that is truncated rather than rounded. The program checks that the whole enclosing ball lies inside one interval [d, d + 10⁻¹⁰⁰⁰).

## Two independent methods (Arb ball arithmetic, FLINT 3.3.1, 3500 bits)

1. **FLINT's `arb_const_catalan`.** The enclosure radius is 2.5·10⁻¹⁰⁵⁴.
2. **Ramanujan's series** G = (π/8) log(2 + √3) + (3/8) Σ_{n≥0} 1/((2n+1)² C(2n,n)), with 1753 terms. For the tail: for n ≥ 1, the ratio of consecutive terms is (n+1)/(2(2n+1)) · ((2n+1)/(2n+3))² ≤ 1/3. So the remainder after the last term t is at most t/2. The enclosure radius is 3.3·10⁻¹⁰⁵¹.

The two balls overlap, and both give the same 1000 decimals.

Note that method 2 is itself a series in the central binomial coefficients C(2n,n), the type-B Catalan numbers.

## Reproduce

```
gcc -O2 -I$FLINT/include catalan_1000.c -o catalan_1000 -L$FLINT/lib -Wl,-rpath,$FLINT/lib -lflint -lmpfr -lgmp -lm
./catalan_1000 > catalan_1000.log
```
