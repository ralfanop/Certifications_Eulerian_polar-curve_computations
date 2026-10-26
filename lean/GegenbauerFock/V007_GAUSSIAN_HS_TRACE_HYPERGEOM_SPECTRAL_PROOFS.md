# V007 — Gaussian Bargmann–Fock isometry, Hilbert–Schmidt trace, hypergeometric formula, and compact spectral theorem

**26 October 2026.** Research-level complete mathematical arguments. **This document is NOT a Lean kernel certificate.** A theorem only becomes formally certified when a corresponding exact Lean declaration compiles, \`#print axioms\` is audited, and a green CI is tied to the precise SHA. The previously proved adjoint/Gram operator equalities are certified separately. No changes to V097; no merge of draft PR #16.

## 1. Definitions and the full Gaussian holomorphic space

Fix \(\alpha>0,\lambda>0\) and put \(p=\lambda+\tfrac12\). Let
\[
d\nu_\lambda(u)=\frac{\Gamma(\lambda+1)}
{\sqrt\pi\,\Gamma(\lambda+\frac12)}
(1-u^2)^{\lambda-\frac12}\mathbf1_{(-1,1)}(u)\,du.
\]
Equivalently \(U=2X-1\) for \(X\sim\operatorname{Beta}(p,p)\).
Define the **full** Bargmann–Fock space (not merely a polynomial
subspace) by
\[
\mathscr F_\alpha=
\left\{F\text{ entire}:
\frac{\alpha}{\pi}\int_{\mathbb C}|F(z)|^2
e^{-\alpha|z|^2}\,dA(z)<\infty\right\}
\]
with polarization
\[
\langle F,G\rangle_{\mathscr F_\alpha}
=\frac{\alpha}{\pi}\int_{\mathbb C}\overline{F(z)}G(z)
e^{-\alpha|z|^2}\,dA(z).
\]
Here the inner product is conjugate-linear in its first argument.

### Theorem A (onto isometry)

For the entire reconstruction
\[
(\mathcal R_\alpha a)(z)
=\sum_{n=0}^\infty a_n\sqrt{\frac{\alpha^n}{n!}}z^n,
\qquad a\in\ell^2(\mathbb N;\mathbb C),
\]
the series is absolutely locally uniformly convergent,
\(\mathcal R_\alpha:\ell^2\to\mathscr F_\alpha\)
is a surjective linear isometry, and
\[
\|\mathcal R_\alpha a\|_{\mathscr F_\alpha}^2
=\sum_{n=0}^\infty |a_n|^2.
\]

**Proof.** Cauchy–Schwarz bounds the series on \(|z|\le R\) by
\(\|a\|_2e^{\alpha R^2/2}\). Hence it is entire.
For the monomials \(z^n\), polar coordinates and angular orthogonality yield
\[
\frac{\alpha}{\pi}\int_{\mathbb C}
\overline{z}^{\,m}z^n e^{-\alpha|z|^2}\,dA(z)
=\delta_{mn}\frac{n!}{\alpha^n}.
\]
For the finite partial polynomial \(P_N\), its squared Fock norm equals
\(\sum_{n=0}^N|a_n|^2\).
For the infinite series, on each circle \(|z|=r\) the angular
Parseval formula gives
\[
\frac1{2\pi}\int_0^{2\pi}|F(re^{i\theta})|^2d\theta
=\sum_{n\ge0}|a_n|^2\frac{\alpha^n r^{2n}}{n!}.
\]
Integrate against the positive radial Gaussian density, and apply
Tonelli (nonnegative terms): the Gaussian norm equals \(\sum|a_n|^2\).
This proves membership and isometry without assuming the completion
identifies with the entire-function space.

Conversely, take any entire \(F(z)=\sum_{n\ge0}b_nz^n\) in
\(\mathscr F_\alpha\). Angular Parseval at each radius followed by Tonelli
gives
\[
\|F\|_{\mathscr F_\alpha}^2
=\sum_{n\ge0}|b_n|^2\frac{n!}{\alpha^n}.
\]
Thus \(a_n=b_n\sqrt{n!/\alpha^n}\in\ell^2\) and
\(\mathcal R_\alpha a=F\). The map is onto. The polarization identity
proves preservation of the full complex inner product. QED.

**Lean boundary A:** require a concrete Gaussian area measure on
\(\mathbb C\simeq\mathbb R^2\), measurable holomorphic \(L^2\)
representatives, a suitable version of circle Parseval, radial
Tonelli, and surjectivity. The existing continuous evaluation on
\(\ell^2\) does **not** by itself prove this theorem.

## 2. Factorial moment coefficients and Hilbert–Schmidt ideal

Define \(c=1/(4\alpha)\) and the genuine bounded operator
\[
C_{\lambda,\alpha}:L^2(\nu_\lambda)\to\ell^2,\qquad
(Cf)_n=i^n\sqrt{\frac{c^n}{n!}}\int_{-1}^{1}u^nf(u)\,d\nu_\lambda(u).
\]
Its adjoint and the exact integral Gram operator were certified in
the previous V007 checkpoint.

### Theorem B (ideal-level Hilbert–Schmidt identity)

The operator \(C\) belongs to the Hilbert–Schmidt ideal and
\[
\boxed{\|C\|_{\mathrm{HS}}^2
=\sum_{n=0}^\infty\frac{c^n}{n!}\int u^{2n}\,d\nu_\lambda(u)
=\int e^{c u^2}\,d\nu_\lambda(u).}
\]

**Proof.** The \(n\)th row of \(C\) is the Riesz functional for
the vector
\(\overline{i^n}\sqrt{c^n/n!}\,u^n\in L^2(\nu_\lambda)\),
whose squared norm is exactly
\[
a_n=\frac{c^n}{n!}\int u^{2n}\,d\nu_\lambda(u).
\]
As \(|u|\le1\) almost everywhere,
\(0\le a_n\le c^n/n!\) and \(\sum a_n\le e^c<\infty\).
For arbitrary orthonormal bases \((e_j)_j\) in the source and
the canonical basis \((\delta_n)_n\) in the target,
Parseval gives
\[
\sum_j\|Ce_j\|_{\ell^2}^2
=\sum_n\sum_j|\langle \delta_n,Ce_j\rangle|^2
=\sum_n\|C^*\delta_n\|_{L^2}^2
=\sum_n a_n<\infty.
\]
All changes of order use Tonelli for nonnegative terms.
This is precisely the Hilbert–Schmidt ideal criterion, and
its norm is the displayed sum. Exchanging the positive
power series of \(e^{cu^2}\) and integration gives the integral
formula. QED.

**Lean boundary B:** the existing \`rowEnergy_eq_exp_integral\`
certifies the infinite row-energy equality; an **additional**
theorem relating the row energies to an explicit ideal
Hilbert–Schmidt type and its canonical norm is required before
claiming the ideal API is certified.

## 3. Explicit ultraspherical moments and confluent hypergeometric function

### Theorem C (all moments)

For every \(n\ge0\),
\[
m_{2n}:=\int u^{2n}d\nu_\lambda(u)
=\frac{(\frac12)_n}{(\lambda+1)_n},
\qquad
m_{2n+1}=0.
\]

**Proof.** The normalized density is even; hence all odd moments
vanish. For even moments substitute \(t=u^2\):
\[
m_{2n}=\frac{B(n+\frac12,\lambda+\frac12)}
{B(\frac12,\lambda+\frac12)}
=\frac{\Gamma(n+\frac12)}{\Gamma(\frac12)}
\frac{\Gamma(\lambda+1)}{\Gamma(n+\lambda+1)}
=\frac{(\frac12)_n}{(\lambda+1)_n}.
\]
The gamma normalization follows from
\(B(\frac12,\lambda+\frac12)=
\sqrt\pi\,\Gamma(\lambda+\frac12)/\Gamma(\lambda+1)\).
For a proof starting instead from the pushforward Beta measure,
use the Beta density and affine change of variables; do not
presuppose the unproved equality of measures. QED.

### Theorem D (exact hypergeometric identity)

For every \(\lambda,\alpha>0\),
\[
\boxed{\|C_{\lambda,\alpha}\|_{\mathrm{HS}}^2
={}_1F_1\left(\frac12;\lambda+1;\frac1{4\alpha}\right).}
\]

**Proof.** Substitute Theorem C into the absolutely convergent
series of Theorem B:
\[
\sum_{n=0}^\infty \frac{c^n}{n!}
\frac{(\frac12)_n}{(\lambda+1)_n}.
\]
By the defining power series this is
\({}_1F_1(\frac12;\lambda+1;c)\).
Since \(0\le m_{2n}\le1\), the series is dominated by \(e^c\)
and is convergent. QED.

**Lean boundary C–D:** first certify measure-density identity (or
pushforward Beta moments directly), then Pochhammer ratio
with gamma recurrence, and finally a precisely defined
\({}_1F_1\) power series/Mathlib special-function identification.
Do not claim Theorem D certified solely because its integrand
is already formalized.

## 4. Gram trace and trace-class ideal

Let \(S=C^*C\), a positive self-adjoint compact operator on
\(L^2(\nu_\lambda)\), with the **already certified** integral kernel
\(K(u,v)=e^{cuv}\).

### Theorem E (trace class)

\(S\) is positive trace-class and
\[
\boxed{\operatorname{Tr}(S)
=\|C\|_{\mathrm{HS}}^2
=\int e^{cu^2}\,d\nu_\lambda(u)
={}_1F_1\left(\frac12;\lambda+1;c\right).}
\]

**Proof.** Hilbert–Schmidt operators have trace-class products
\(C^*C\), and \(\operatorname{Tr}(C^*C)
=\|C\|_{\mathrm{HS}}^2\) by the trace definition and Tonelli/Parseval.
The remaining equalities are Theorems B and D. QED.

**Lean boundary E:** implement a trace-class ideal or suitable
positive trace functional; prove the relevant ideal-product theorem
and \(\operatorname{Tr}(C^*C)\), not just canonical
coefficient-row energy. In an infinite-dimensional space,
trace is **not** defined for every bounded operator.

## 5. Full compact self-adjoint spectral structure

### Theorem F (strict positivity, injectivity, dense range)

The Gram operator \(S\) is positive, compact, self-adjoint and
injective. In fact \(\ker C=\ker S=\{0\}\), and
\(\overline{\operatorname{ran}S}=L^2(\nu_\lambda)\).
The map \(C:L^2(\nu_\lambda)\to\ell^2\) has dense range.

**Proof.** Positivity, compactness, and self-adjointness of
\(S=C^*C\) have already been proved for the concrete operator.
If \(Cf=0\), every moment vanishes:
\(\int u^nf(u)\,d\nu_\lambda(u)=0\) for all \(n\ge0\).
Thus \(f\) is orthogonal to every polynomial. Since the
ultraspherical measure is a finite Borel probability measure with
support contained in \([-1,1]\), continuous functions are dense
in \(L^2(\nu_\lambda)\), and (by Weierstrass) polynomials are
uniformly dense in \(C([-1,1])\). Hence polynomials are
dense in \(L^2(\nu_\lambda)\), so \(f=0\).
The Gram kernel equals the kernel of \(C\), because
\(\langle Sf,f\rangle=\|Cf\|^2\), hence \(\ker S=0\).
As \(S\) is self-adjoint, \((\operatorname{ran}S)^\perp
=\ker S^*=\ker S=0\), establishing dense range.

For density of \(\operatorname{ran}C\), assume \(C^*a=0\).
The already certified analytic adjoint formula says the entire
Fock reconstruction of \(a\) is zero on the support of
\(\nu_\lambda\), almost everywhere. The measure has strictly
positive density on \((-1,1)\), so the zero set is dense
in this interval (indeed its complement has measure zero);
continuity forces the entire reconstruction to vanish on
\((-1,1)\). The analytic identity theorem forces it to
vanish everywhere, and uniqueness of Taylor coefficients gives
\(a=0\). Hence \(\ker C^*=0\), yielding dense range of \(C\).
Note: proving density of \(\operatorname{ran}C\) genuinely
requires positive mass in every open subinterval, in addition
to the already certified closed-support inclusion. QED.

### Theorem G (spectral expansion)

There exists a complete orthonormal basis
\((\phi_j)_{j\ge0}\) of \(L^2(\nu_\lambda)\) consisting
of eigenvectors of \(S\), with positive eigenvalues
\(\sigma_j^2>0\), counted with multiplicity, satisfying
\(\sigma_j\to0\). Moreover
\[
S f=\sum_{j\ge0}\sigma_j^2\langle\phi_j,f\rangle\phi_j,
\qquad
\sum_{j\ge0}\sigma_j^2=
{}_1F_1\left(\frac12;\lambda+1;c\right).
\]
The operator \(C\) admits a singular-value decomposition with
singular values \(\sigma_j\), and \(\sum_j\sigma_j^2<\infty\).

**Proof.** Apply the compact self-adjoint spectral theorem to
\(S\). Injectivity excludes zero eigenvectors; positivity
excludes negative eigenvalues. The measure is non-atomic and
has a positive density on \((-1,1)\), so its complex
\(L^2\) space is infinite-dimensional. Thus positive eigenvalues
can be enumerated (with finite multiplicities) and accumulate
only at zero. The trace equals the sum of the positive
eigenvalues by the positive trace-class spectral theorem.
Set \(\sigma_j=\sqrt{\lambda_j(S)}\).
Then \(C\phi_j/\sigma_j\) is an orthonormal system in
\(\ell^2\), with
\[
\langle C\phi_j,C\phi_k\rangle
=\langle S\phi_j,\phi_k\rangle
=\sigma_j^2\delta_{jk}.
\]
Density of \(\operatorname{ran}C\) makes this system complete,
giving the full singular-value decomposition. QED.

**Precision:** \(\sigma_j\) need not be summable: Hilbert–Schmidt
implies \(\sum_j \sigma_j^2<\infty\), i.e. \(C\in S_2\);
it does **not** imply \(C\in S_1\).
However \(S=C^*C\in S_1\). No exact closed-form individual
eigenvalues are being claimed.

**Lean boundary F–G:** formal polynomial density for the
pushforward ultraspherical measure; use it for injectivity
and dense range, formalize positive-density support and analytic
identity theorem; invoke Mathlib compact self-adjoint spectral
API with the correct positivity and separability hypotheses.
Trace and singular-value identities require the ideal
structures from Theorems B/E.

## 6. Verifiable decomposition and status register

| Component | Mathematical proof in this dossier | Lean theorem/CI |
|---|---|---|
| Full onto Gaussian Fock isometry | Theorem A | **NOT YET CERTIFIED** |
| Actual coefficient operator, adjoint, Gram | Prior V007 proofs | **CERTIFIED** at workflow 40386146429 |
| HS row energy = exponential integral | Theorem B (row-energy part) | **CERTIFIED** in RowEnergyExpIntegral.lean |
| HS ideal API equality | Theorem B (ideal part) | **NOT YET CERTIFIED** |
| General ultraspherical moments | Theorem C | **NOT YET CERTIFIED** |
| Confluent hypergeometric identity | Theorem D | **NOT YET CERTIFIED** |
| Gram trace class and trace | Theorem E | **NOT YET CERTIFIED** |
| Gram positive, self-adjoint, compact | Theorem F (operator part) | **CERTIFIED** in existing modules |
| Injectivity and both dense-range claims | Theorem F (density part) | **NOT YET CERTIFIED** |
| Complete compact spectral expansion / singular values | Theorem G | **NOT YET CERTIFIED** |

The branch is a **draft PR**, not merged. All Lean dependencies
must be checked at the SHA where the specific statements exist;
a CI success does not certify the paper-level claims above.
