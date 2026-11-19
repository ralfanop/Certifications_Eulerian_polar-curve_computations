# M15 §6.6: Binet-to-Möbius and Laplace-to-energy proof route (2026-11-19)

Frozen author source: Manuscript_15_AI_Declaration_20261118(1).zip,
SHA-256 e83c1df38752aa85aa580ab31bc24bea56ee4f7f7fc2d84fa97e50df303638aa.
Track eq:stirling-spectral-expansion, eq:mobius-binet-exact,
eq:sine-integral-prime-energy, eq:sine-integral-energy-tail.
This note is an analytic derivation, not a Lean certification of all four
identities. No changed manuscript or figure. PR #369 is the certified
absolute-summability and regrouping dependency.

## Binet: a route avoiding a separate coth partial-fraction theorem

For x>0 set R(x)=log Gamma(x)-(x-1/2)log(x)+x-(1/2)log(2*pi).
Use the classical second Binet integral (NIST DLMF 5.9.10,
https://dlmf.nist.gov/5.9.E10). For t>0 the expansion of
1/(exp(2*pi*t)-1) into sum_{n>=1} exp(-2*pi*n*t) is a nonnegative
geometric series. Since arctan(t/x)>=0, Tonelli gives

R(x)=2 sum_{n>=1} int_0^infty arctan(t/x) exp(-2*pi*n*t) dt.

For b=2*pi*n>0 integrate by parts. At 0 the boundary vanishes;
at infinity arctan(t/x) is bounded by pi/2 and exp(-b*t) tends to 0.
The derivative of arctan(t/x) is x/(x^2+t^2); both resulting integrals
converge, for example by domination by constants times exp(-b*t).
Thus the nth summand (including 2) is

(2/b) int_0^infty exp(-b*t) x/(x^2+t^2) dt
= 2*x int_0^infty exp(-u)/(u^2+b^2*x^2) du,

after u=b*t. At positive integer x=m this proves
R(m)/m = sum_{n>=1} K(m*n), where K is exactly laplaceKernel from #369.
The bound K(k)<=2/(4*pi^2*k^2) from #369 gives absolute summability of
the double family with weights mu(m). No conditional exchange is needed:
sum_{m>=1} mu(m)*R(m)/m = K(1). All identification steps involving Gamma,
Binet, arctan integration by parts, and the Tonelli interchange remain
Lean obligations, not inferred from numerical checks.

## Laplace-to-energy: nonnegative Tonelli route

Put a=2*pi and define F(s,t)=s exp(-s*t)(1-cos(t)), s>0, t>a.
This is continuous and nonnegative. For each t>a,

int_0^infty s exp(-t*s) ds = 1/t^2

by u=t*s and the elementary Gamma(2)=1 integral.

For each s>0, an antiderivative of F in t is

P(s,t)=exp(-s*t) [s^2(cos(t)-1)-s sin(t)-1]/(s^2+1).

Differentiate explicitly; P tends to zero as t->infinity, since the
bracket is bounded, and P(s,a)=-exp(-s*a)/(s^2+1). Hence

int_a^infty F(s,t) dt = exp(-a*s)/(s^2+1).

Tonelli applied to the actual nonnegative F (not the conditionally
convergent sin(t)/t integral) gives

int_a^infty (1-cos(t))/t^2 dt
= int_0^infty exp(-a*s)/(s^2+1) ds
= a int_0^infty exp(-u)/(u^2+a^2) du = pi*K(1).

Finiteness follows also from 0<=1-cos(t)<=2 and a>0.
For the real removable sinc rE(t)=sin(t/2)/(t/2), its square equals
2(1-cos(t))/t^2 off zero. The exact Plancherel normalization
int_R rE(t)^2 dt=2*pi and the already established central-window
integral in EulerianCert/KrapivskyLuckEnergy.lean then give

K(1)=(1/(4*pi)) int_{|t|>2*pi} rE(t)^2 dt
= 1/2 - Si(2*pi)/pi.

In particular this route never treats sin(t)/t on a half-line as
Lebesgue integrable. The Plancherel input must be proved or separately
located in the certified dependency chain before claiming the full Lean
identity. The Lean module on this branch implements the actual damped
cosine section, including derivative, limit and integral, and the
exact scaling of K(1); compilation and whitelist audit are pending.
The Gamma(2) section, product-measure Tonelli, and final energy bridge
are still to be formalized. Existing #369 Arb artifacts certify scalar
expressions; no new numerical certification is asserted here.
