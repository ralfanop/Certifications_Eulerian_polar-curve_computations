# V007 — rigorous rational enclosure of a Gegenbauer–Fock scalar integral

## Kernel-verified Eulerian uniform law — 2 November 2026

The previously separate identification of the abstract ultraspherical
probability law with the *actual uniform Lebesgue density* is now a
Lean kernel certificate.

- **[CI #41436401805](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41436401805): SUCCESS**, 9,021 build jobs; source
  [`UltrasphericalLegendreDensityExact.lean`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/af90d0c6605b842521274d7fb6bdf7d830637fff/lean/GegenbauerFock/UltrasphericalLegendreDensityExact.lean).
- `gammaDensity_half_eq_eulerianUniformDensity` is the pointwise
  density equality for every real argument, including zero outside
  the open support.
- `measure_half_eq_uniformDensity` identifies the original
  Beta-pushforward measure exactly with Lebesgue measure weighted by
  `(1/2) * 1_{(-1,1)}`, as genuine measures.
- `integral_measure_half_eq_uniformDensity` transfers real Bochner
  integrals to this normalized Lebesgue measure.

Every individual `#print axioms` audit is clean: only
`propext`, `Classical.choice`, `Quot.sound`, without `sorryAx`
or `Lean.ofReduceBool`.

**Scope:** This certificate establishes the equality of probability
measures and their real integrals. Translating this into the literal
interval-integral notation printed in the paper is a separate
notation/measure-restriction bridge. The operator-specific S₂
energy and Gram trace decimal enclosures have their own dedicated
CI and must not be marked certified unless that run completes green.

## Kernel-verified update — 2 November 2026

The original 26 October status notes below record the **historical**
boundary; the following later certifications supersede their claim that
the infinite Taylor remainder was not formalized.

- **CI [41432703183](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41432703183): SUCCESS**, 9,014 build jobs. Lean proves `fifteen_tail_strict_bound` and
  `fifteen_rational_endpoints`, including the infinite positive-series
  remainder and strict outward rational 24-place endpoints.
- **CI [41433829109](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/41433829109): SUCCESS**, 9,039 build jobs; exact source commit
  [`2e81430a`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/commit/2e81430a63a67670bf2dff7e02b368ce6863a100).
  Its six audited declarations include `kummer_ratio_half`,
  `kummer_half_quarter_eq_realTraceSeries`,
  `legendre_exp_integral_eq_realTraceSeries`, and
  `legendre_exp_integral_decimal_enclosure`.
- Both audits report only `propext`, `Classical.choice`, and
  `Quot.sound` in the theorem dependencies: no `sorryAx` or
  `Lean.ofReduceBool`.

The certified integral is the **actual ultraspherical probability measure**
integral
`∫ u : ℝ, Real.exp (u^2 / 4) ∂(Ultraspherical.measure (1/2))`.
The proven exact series is
`∑' n : ℕ, 1/(4^n * n! * (2*n+1))`, with the same strict
24-decimal enclosure printed in V007.2. This is an unconditional
infinite-series and actual-measure statement, not just finite
arithmetic or floating-point evidence.

**Separate final correspondence check:** the literal manuscript notation
`(1/2) ∫_{-1}^1 exp(u^2/4) du` additionally uses the
specialization of the ultraspherical law to uniform Lebesgue density
`1/2` on the interval. Likewise, any formulation in terms of the
norm in a named Hilbert–Schmidt ideal must cite its exact checked
operator-to-energy identification, not merely infer it from this scalar
certificate. Neither stronger correspondence is silently asserted by
the six theorems above.



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
