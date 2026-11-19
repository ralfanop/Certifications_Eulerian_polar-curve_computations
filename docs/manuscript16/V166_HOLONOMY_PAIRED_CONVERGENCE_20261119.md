# M16.6 §14.5 — scalar paired holonomy product convergence

Frozen source label eq:hol-det; continuation of #346 and its exact paired
numerator. Distinct from #424 (Schur), #430 (Schatten scalar tails), and
#436 (finite-rank cutoff). No geometric operator or spectral determinant
identity is asserted. The scalar product convergence is proved analytically;
the accompanying five Lean declarations are candidates until exact-HEAD CI.

For a>0, phi real and integer n>=1 let
```
R_n = [((n-phi)^2+a^2)((-n-phi)^2+a^2)]/(n^2+a^2)^2
C = 2 phi^2(a^2+1)+phi^4.
```
Every R_n is positive. Expanding the numerator gives
R_n-1 = [2 phi^2(a^2-n^2)+phi^4]/(n^2+a^2)^2.
The absolute numerator is at most 2 phi^2(a^2+n^2)+phi^4 <= C n^2,
because n^2>=1. The denominator is at least n^4. Consequently
|R_n-1| <= C/n^2 and the deviations are absolutely summable.

Choose N>=1 with C/(N+1)^2 <= 1/2. By the mean value theorem for log,
|log R_n| <= 2 |R_n-1| for n>N. The integral comparison gives
sum_{n>N}|log R_n| <= 2C/N. Hence the paired scalar product P_N =
prod_{n=1}^N R_n converges to a strictly positive P, with
exp(-2C/N) <= P/P_N <= exp(2C/N).
The unpaired n=0 factor (a^2+phi^2)/a^2 is positive and finite.

For a and phi varying in compact subsets of a>0 and phi real, C has a
uniform upper bound and the finite factors are continuous and strictly
positive. The same estimate proves local uniform convergence and
nonvanishing in these real parameters. This establishes the existence of
the symmetrically paired product, not its evaluation by the Euler sine
product or its identification as an operator determinant.

Lean candidates: positivity, exact difference, nonnegative majorant,
pointwise bound and actual infinite Summable of absolute deviations.
The logarithmic/product argument and Euler closed evaluation remain
separate Lean obligations. No new numerical constant; no Arb claim.
No manuscript edits or merge.
