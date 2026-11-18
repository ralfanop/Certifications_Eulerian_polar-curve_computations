# M12 limit profile: rigorous-certification plan (18 November 2026)

Source lock: `Manoscritto_12_20261118(1).zip`, SHA-256 `7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860`.

## Exact analytic reduction (not a numerical certificate)

For the centered uniform law, set
`Lambda(s)=log(sinh(s/2)/(s/2))`, `x(s)=Lambda'(s)=coth(s/2)/2-1/s` for positive real `s`.
The map `x:(0,infinity)->(0,1/2)` is strictly increasing, since `Lambda''(s)` is the positive variance of the exponentially tilted uniform law. Write `s(x)` for its inverse. For `0<a<1/2` define

`H(a)=(1/pi)*integral_{0}^{pi/2} a*sin(theta)*s(a*sin(theta)) dtheta`,
`H(a_alpha)=alpha`, and `F(alpha)=a_alpha^2/4`.

Substitution `u=sin(theta)` yields the equivalent weighted integral

`H(a)=(a/pi)*integral_{0}^{1} u*s(a*u)/sqrt(1-u^2) du`.

This substitution removes endpoint trigonometric evaluation but **does not remove inverse Langevin evaluation**. An implementation must not claim that it does.

For numerical certification, prove a validated interval bracket `a_lo<a_alpha<a_hi` using strict interval inequalities `H(a_lo)<alpha<H(a_hi)`; then interval-square the bracket to enclose `F(alpha)`. Evaluate the integral with an explicit analytic-tail or interval quadrature remainder, not merely floating-point quadrature. To reach 1,000,001 significant digits, a low-order subdivision method is insufficient: obtain uniform complex-analytic bounds on a transformed integrand and a spectral/tanh-sinh or Taylor remainder with verified constants. The inverse `s(x)` also needs validated root brackets on the quadrature domain.

## Finite-M recurrence coefficients

The moments of a sum of M centered independent uniforms are rational: `mu_0=1` and `mu_k=sum_{j=0}^k binom(k,j) mu_j^{(M-1)} mu_{k-j}^{(1)}`, where the single-uniform moment is `0` for odd k and `1/((k+1)*2^k)` for even k. Hence each finite-M Jacobi/Lanczos coefficient is **exactly rational** when expressed by Hankel determinants or an exact Stieltjes recurrence (assuming the relevant Hankel determinants are nonzero). Compute these 20 coefficients with exact integer/rational arithmetic, not Arb; then enclose their discrepancies with the certified `F(alpha)` balls. The 20 discrepancies must not be labelled million-digit-certified before the five profile balls pass the same exact rounding-cell test.

## Coverage and non-claims

- PROVED (mathematical): the substitution identity, rationality of finite-M moments and recurrence coefficients.
- CONDITIONAL: rigorous finite-M discrepancies after certified profile evaluations.
- OPEN: the five million-digit `F(alpha)` enclosures, explicit quadrature/root remainders and the 20 associated discrepancies.
- Independent scalar values: PR #384, whose exact-head CI must be checked separately. This note does not certify the manuscript as a whole.

No manuscript or figure is modified.
