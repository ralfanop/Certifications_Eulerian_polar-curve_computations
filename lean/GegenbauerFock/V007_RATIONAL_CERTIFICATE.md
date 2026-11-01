# V007 — rigorous rational enclosure of a Gegenbauer–Fock scalar integral

**26 October 2026.** This numerical certificate is for the *scalar integral*
\[
I=\frac12\int_{-1}^{1}\exp(u^2/4)\,du,
\]
corresponding to \(\lambda=\tfrac12,\alpha=1\). The identification
\(I=\|C_{1/2,1}\|_{\mathrm{HS}}^2\) is justified mathematically in
\`V007_HILBERT_PROOF_DOSSIER.md\` but **is not yet a certified Lean
operator-theory theorem**.

## Exact rational interval, with no floating-point operations

The Lean-verified Legendre moments give
\[
I=\sum_{n=0}^{\infty}\frac{1}{4^n n!(2n+1)}.
\]
Let
\[
S_{15}=\sum_{n=0}^{14}\frac{1}{4^n n!(2n+1)}
=\frac{337212679483569969430703669}{309376751206532288348160000}.
\]

For \(n\ge15\), \(n!\ge15!(n-15)!\), and \(2n+1\ge1\); thus
\[
0<I-S_{15}
\le\sum_{n=15}^{\infty}\frac{4^{-n}}{n!}
\le\frac{4^{-15}}{15!}e^{1/4}
<\frac{4^{-15}}{15!}\frac43
=\frac{1}{1053078495820775424000}.
\]
We used the positive-term comparison \(e^{1/4}<\sum_{k\ge0}4^{-k}=4/3\).
Consequently,
\[
\boxed{
\frac{337212679483569969430703669}{309376751206532288348160000}
<I<
\frac{142666902858433448605421999}{130890163971994429685760000}
}.
\]
This exact rational interval implies the outward-rounded decimals
\[
\boxed{
1.089974208367244447324816
<I<
1.089974208367244447325767.
}
\]
The decimal lines are strict outward roundings of the rational bounds.

## Certification status

- The Legendre moment identity for every nonnegative integer is
  already checked in \`LegendreMoments.lean\`.
- The *exact arithmetic identities* for \(S_{15}\) and the upper
  endpoint are targeted by \`RationalTrace.lean\`, using the kernel-safe
  \`norm_num\` tactic (not \`native_decide\`).
- The positivity/Taylor-remainder comparison above is a rigorous
  written proof, **not yet a Lean theorem**.
- No Arb/mpmath.iv floating-point or numerical interval inference is
  necessary for this certificate; the bounds are exact rationals.
- This is a single illustrative scalar case, not a claim of full
  operator, general-\(\lambda\), or spectral certification.
