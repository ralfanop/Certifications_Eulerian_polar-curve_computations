# Exact rational exponentially convergent enclosure for the det4 fourth moment

Scope: diagonal Schatten-4 test model in Drafts #373/#376. This is a classical Euler transformation of the Dirichlet eta series, **not** a Lean proof, FLINT/Arb certificate, or a physical-operator identification. No protected manuscript/figure edits.

For real s>0 and n>=0 define the finite difference
```
d_n(s) = sum_{k=0}^n (-1)^k binomial(n,k)/(k+1)^s.
```
The gamma-integral representation (valid s>0) yields
```
d_n(s) = 1/Gamma(s) * integral_0^infinity t^(s-1)*exp(-t)*(1-exp(-t))^n dt.
```
Consequently 0<d_n(s)<=1, with strict inequality for n>0. Euler's transform of the alternating Dirichlet series gives the absolutely convergent identity
```
eta(s) = sum_{n=0}^infinity d_n(s)/2^(n+1)
       = (1-2^(1-s))*zeta(s)       (s>1).
```
For completeness, the transform follows by applying the binomial theorem to the finite differences and then using the gamma-integral representation with Tonelli: sum_n 2^(-n-1)(1-exp(-t))^n = 1/(1+exp(-t)); the resulting integral is the standard eta integral.

For integer N>=1, put E_N(s)=sum_{n=0}^{N-1} d_n(s)/2^(n+1), an **exact rational number** when s is a positive integer. Positivity and d_n(s)<=1 prove
```
0 < eta(s)-E_N(s) < 2^(-N)    (s>0).
```
For A=Tr(T^4)=zeta(2)-zeta(3), set
```
A_N^Euler = (4/3)*E_N(2) - (8/7)*E_N(3).
```
Since zeta(2)=4 eta(2)/3 and zeta(3)=8 eta(3)/7, the following **exact rational enclosure** holds:
```
A_N^Euler - (8/7)*2^(-N) < A < A_N^Euler + (4/3)*2^(-N).
```
Its width is (52/21)*2^(-N), exponentially smaller than the O(1/N) interval in the earlier note. This is a rigorous interval independent of any floating-point library. For c4=-A/4 and D4''''(0)=-6A, multiply the endpoints with reversed order as appropriate.

This bound is a **mathematical acceleration route**, not a claim of feasible 1,000,001-digit computation. A naive implementation of the nested binomial sums requires quadratic work and huge exact rationals; a production implementation must use fast transforms or Arb's rigorously bounded zeta routines and individually assert ctx.prec=3600000 and rel_accuracy_bits()>=3400000 for nonzero quantities, then verify strict inclusion of the entire Arb ball in a single 1,000,001-significant-digit rounding cell using exact endpoints. Do not claim coverage or certification from the rational inequality alone.

Lean obligations: finite binomial identity, positivity via integral or Hausdorff moments, summation/interchange, eta-to-zeta identity, rational enclosure. Classical mathematics, no originality claim. No merge.
