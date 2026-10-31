# V007 — Gaussian Fock isometry, Hilbert–Schmidt ideal, trace, confluent hypergeometric and spectral theory

**Mathematical proof dossier. 26 October 2026.**
This document **is not a Lean certificate**. For every theorem below, a
separate exact-sha kernel compilation and axiom audit is required before
the theorem may be reported as *formally certified*. Previously certified
facts about the concrete bounded/compact operator and analytic adjoint
are cited by name below. This is for the separate V007 manuscript;
approved V097 and main are untouched.

## Definitions and normalization

Fix \(\lambda>0\), \(\alpha>0\) and \(c=1/(4\alpha)>0\).
Let \(\nu_\lambda\) be the symmetric beta-pushforward
\(2X-1\), \(X\sim{\rm Beta}(\lambda+\tfrac12,\lambda+\tfrac12)\).
Its explicit normalized density is

\[
d\nu_\lambda(u)=
\frac{\Gamma(\lambda+1)}
 {\sqrt{\pi}\,\Gamma(\lambda+\tfrac12)}
 (1-u^2)^{\lambda-\frac12}{\bf1}_{(-1,1)}(u)\,du.
\tag{M1}
\]

Mathlib already certifies this measure's probability normalization and
support, **not** the formula (M1) as an equality of measures.

The complex Gaussian probability measure on the plane is
\[
d\gamma_\alpha(z)=\frac{\alpha}{\pi}
e^{-\alpha|z|^2}\,dA(z).\tag{F1}
\]
The holomorphic Gaussian Hilbert space \(\mathcal F_\alpha\)
consists of entire functions \(H\) with
\(\|H\|_{\mathcal F_\alpha}^2=\int_{\mathbb C}|H|^2d\gamma_\alpha<\infty\).
Inner products are **conjugate linear in the first argument**.

## A. Complete Gaussian Bargmann–Fock isometry

**Theorem A.1 (unitary entire-function realization).**
For all \(\alpha>0\), the reconstruction
\[
 {\cal R}_\alpha:\ell^2(\mathbb N;\mathbb C)\longrightarrow
 \mathcal F_\alpha,\quad
 F\longmapsto \sum_{n=0}^\infty F_n
 \sqrt{\frac{\alpha^n}{n!}}\,z^n
 \tag{F2}
\]
is a surjective complex-linear isometry.

**Proof.** By Cauchy–Schwarz and
\(\sum\alpha^n|z|^{2n}/n!=e^{\alpha|z|^2}\), the series converges
absolutely, locally uniformly and normally on the plane, hence is
entire. For a polynomial \(P(z)=\sum_{n=0}^N a_nz^n\), polar
coordinates and angular orthogonality give
\[
\begin{aligned}
\int_{\mathbb C}|P(z)|^2d\gamma_\alpha(z)
 &=\frac{\alpha}{\pi}
 \int_0^\infty e^{-\alpha r^2}r\,dr
 \int_0^{2\pi}\sum_{n,m}a_n\overline{a_m}
 r^{n+m}e^{i(n-m)\theta}d\theta\\
 &=\sum_{n=0}^N |a_n|^2\frac{n!}{\alpha^n};
 \qquad
 2\alpha\int_0^\infty r^{2n+1}e^{-\alpha r^2}dr
 =\frac{n!}{\alpha^n}.
\end{aligned}\tag{F3}
\]
For the entire function \(H(z)=\sum_{n\ge0}a_nz^n\),
the Taylor series converges uniformly on each circle
\(|z|=r\). Circular Parseval gives the **nonnegative** identity
\[
 \frac1{2\pi}\int_0^{2\pi}|H(re^{i\theta})|^2d\theta
 =\sum_{n\ge0}|a_n|^2r^{2n}.\tag{F4}
\]
Tonelli applied to (F4) and the radial Gaussian integral gives
\[
 \int_{\mathbb C}|H|^2d\gamma_\alpha
 =\sum_{n\ge0}|a_n|^2\frac{n!}{\alpha^n},
 \tag{F5}
\]
allowing the value \(+\infty\) before restricting to
\(\mathcal F_\alpha\). Thus (F2) defines an isometry.
Conversely every \(H\in\mathcal F_\alpha\) has Taylor coefficients
\(a_n\), and (F5) gives \(F_n=a_n\sqrt{n!/\alpha^n}\in\ell^2\)
with \({\cal R}_\alpha F=H\). This proves surjectivity and
completeness. Reproducing kernels are
\(k_w(z)=e^{\alpha z\overline w}\), with
\(\|k_w\|^2=e^{\alpha|w|^2}\). \(\square\)

**Lean boundary:** coefficient-space evaluation and Gaussian
pointwise norms are kernel-certified already. The Gaussian
plane measure, angular Parseval, polar-coordinate Gaussian monomial
integral and surjectivity (F5) still require formalization before
claiming this **entire-function** isometry is Lean certified.

## B. Genuine Hilbert–Schmidt class and its ideal property

Let \(H=L^2(\nu_\lambda;\mathbb C)\) and
\(K=\ell^2(\mathbb N;\mathbb C)\).
The previously certified bounded transform is
\[
 (Cf)_n=i^n\sqrt{\frac{c^n}{n!}}
   \int_{-1}^1u^nf(u)\,d\nu_\lambda(u).\tag{H1}
\]
Writing
\(\psi_n(u)=\overline{i^n}\sqrt{c^n/n!}\,u^n\), we have
\((Cf)_n=\langle\psi_n,f\rangle_H\).

**Theorem B.1 (basis-independent Hilbert–Schmidt norm).**
\(C\) is Hilbert–Schmidt, with
\[
 \|C\|_{\mathcal S_2}^2
 =\sum_{n\ge0}\|\psi_n\|_H^2
 =\int_{-1}^1e^{cu^2}\,d\nu_\lambda(u).\tag{H2}
\]

**Proof.** Let \(\{b_j\}_{j\in J}\) be an arbitrary orthonormal
basis of \(H\). For a Hilbert operator \(T:H\to K\),
\(\|T\|_{\mathcal S_2}^2:=\sum_{j\in J}\|Tb_j\|_K^2\),
where nonnegative sums are understood as suprema of finite sums.
Two applications of Tonelli to the nonnegative double family,
and Parseval in \(H\), give
\[
 \sum_j\|Cb_j\|_K^2
 =\sum_n\sum_j|\langle\psi_n,b_j\rangle|^2
 =\sum_n\|\psi_n\|_H^2.\tag{H3}
\]
The right-hand side is finite:
\[
 \sum_n\|\psi_n\|^2
 =\int\sum_n \frac{c^nu^{2n}}{n!}\,d\nu_\lambda(u)
 =\int e^{cu^2}\,d\nu_\lambda(u)
 \le e^c.\tag{H4}
\]
Thus (H3) establishes the independence of the source basis.
For arbitrary bounded operators \(A:K\to K'\) and \(B:H'\to H\),
the ideal inequalities
\[
 \|AC\|_{\mathcal S_2}\le\|A\|\|C\|_{\mathcal S_2},
\qquad
 \|CB\|_{\mathcal S_2}\le\|C\|_{\mathcal S_2}\|B\|
 \tag{H5}
\]
follow from the definition and the adjoint Hilbert-space Parseval
identity; in particular \(\mathcal S_2\) is a two-sided operator ideal.
\(\square\)

**Lean boundary:** the source-independent sum of *target row*
squared norms is already certified (also its exponential integral),
but equivalence to arbitrary source ONB sums (H3), the two-sided
ideal properties (H5), and a separately packaged \(\mathcal S_2\)
structure require additional Lean declarations. Current pinned
Mathlib does not expose an already packaged Hilbert–Schmidt or
Schatten API under those names.

## C. Nuclear trace of the true Gram operator

Let \(S=C^*C\), whose equality with the actual integral operator
\((Sf)(u)=\int e^{cuv}f(v)\,d\nu_\lambda(v)\) has already been
kernel-certified as a bounded \(H\to H\) operator identity.

**Theorem C.1 (trace class, exact trace).** \(S\) is positive,
self-adjoint and trace-class with
\[
 S=\sum_{n\ge0}|\psi_n\rangle\langle\psi_n|,
 \qquad
 \operatorname{tr}S
 =\sum_n\|\psi_n\|^2
 =\|C\|_{\mathcal S_2}^2
 =\int e^{cu^2}\,d\nu_\lambda(u).\tag{T1}
\]
The rank-one series converges absolutely **in trace norm**, since
each positive rank-one summand has trace norm \(\|\psi_n\|^2\)
and the sum is finite by (H4). In particular convergence also
holds in operator norm and pointwise in \(H\). For any ONB
\(\{b_j\}\subset H\),
\[
 \sum_j \langle b_j,Sb_j\rangle
 =\sum_j \|Cb_j\|^2
 =\sum_n\|\psi_n\|^2,
 \tag{T2}
\]
by Tonelli, so the trace is basis-independent. \(\square\)

**Lean boundary:** the row-energy scalar integral is certified.
The constructive operator-norm nuclear series, separate trace-norm
summability and source-basis-independent trace formula (T2) are
separate formal targets; a summable operator-norm rank-one
decomposition alone is *not* silently called a \(\mathcal S_1\)
certificate.

## D. General ultraspherical moments and \({}_1F_1\)

**Theorem D.1.** With \(m_k=\int u^k\,d\nu_\lambda(u)\),
\[
 m_{2n+1}=0,\qquad
 m_{2n}=\frac{(\frac12)_n}{(\lambda+1)_n}
 \quad(n\ge0).\tag{U1}
\]

**Proof.** The density (M1) is even, giving all odd moments
zero by substitution \(u\mapsto-u\). By the substitution
\(t=u^2\) in the even integral,
\[
 m_{2n}
 =\frac{\int_0^1t^{n-1/2}(1-t)^{\lambda-1/2}dt}
       {\int_0^1t^{-1/2}(1-t)^{\lambda-1/2}dt}
 =\frac{B(n+\frac12,\lambda+\frac12)}
       {B(\frac12,\lambda+\frac12)}.
 \tag{U2}
\]
Using \(B(x,y)=\Gamma(x)\Gamma(y)/\Gamma(x+y)\) and
\((a)_n=\Gamma(a+n)/\Gamma(a)\) for \(a>0\) gives (U1).
All integrals are absolutely convergent because \(\lambda>0\).
\(\square\)

**Theorem D.2 (general hypergeometric trace).** For \(\lambda,\alpha>0\),
\[
 \boxed{\operatorname{tr}S=\|C\|_{\mathcal S_2}^2
 ={}_1F_1\!\left(\frac12;\lambda+1;\frac1{4\alpha}\right)}.
 \tag{U3}
\]
Indeed, since \(e^{cu^2}=\sum_n c^n u^{2n}/n!\) with
nonnegative summands on the support, Tonelli and (U1) give
\[
 \int e^{cu^2}\,d\nu_\lambda
 =\sum_{n\ge0}\frac{(\frac12)_n}{(\lambda+1)_n}
   \frac{c^n}{n!},
 \tag{U4}
\]
which is precisely the *unregularized* Kummer confluent
hypergeometric function. In Mathlib's available **regularized**
generalized hypergeometric convention, the same function equals
\[
 \Gamma(\lambda+1)\;
 {}_1\widetilde F_1(\tfrac12;\lambda+1;c),
 \tag{U5}
\]
not simply \({}_1\widetilde F_1\): the extra Gamma factor is
essential. \(\square\)

**Lean boundary:** (U1), the identification of (U4) with
Mathlib's regularized generalized hypergeometric coefficients,
and the full trace-norm statement are *not yet* certified.
The pinned Mathlib release does contain
\`Complex.regularizedHGFun\` with explicit Gamma
denominators, so (U5) can eventually be built without changing
the pinned toolchain.

## E. Actual spectral resolution

**Theorem E.1 (compact positive Gram spectral theory).**
The positive self-adjoint operator \(S\) is compact and admits
an orthonormal basis of eigenvectors, with nonnegative eigenvalues
of finite multiplicity away from \(0\). Every nonzero eigenvalue
is isolated and the nonzero spectrum can accumulate only at zero.
Its eigenvalue sequence (counted with multiplicity) is summable:
\[
 \sum_j s_j(S)=\operatorname{tr}S
 ={}_1F_1(\tfrac12;\lambda+1;c),
 \quad
 s_j(C)=\sqrt{s_j(S)}.
 \tag{S1}
\]
The first equality uses positivity and trace class; the second
is the definition of the singular values through \(C^*C\).
The nonzero eigenspaces have finite dimension and the closed
span of eigenspaces is all of \(H\). \(\square\)

**Further injectivity statement (mathematical).** Since all moments
\(\int u^nf(u)d\nu_\lambda\) vanish when \(Cf=0\), density of
polynomials in \(L^2(\nu_\lambda)\) forces \(f=0\). This uses
Weierstrass approximation on [-1,1], finite regular measure and
strictly positive interior density. Consequently \(S\) has trivial
kernel and its eigenvalues are strictly positive; \(0\) remains a
spectral accumulation point for infinite-rank \(S\).
Likewise \(C^*F=0\) implies the entire reconstruction vanishes
on the imaginary interval and therefore vanishes identically
by the holomorphic identity theorem; hence \(F=0\) and
the range of \(C\) is dense in \(\ell^2\).
These injectivity and dense-range claims have *not* yet been
kernel-certified.

**Lean boundary:** positive, self-adjoint and compact status is
already certified. The Mathlib infinite-dimensional spectral
theorem (orthogonal complement of the eigenspaces is zero,
finite dimensionality of nonzero eigenspaces) can be specialized
directly. Formal proofs of spectral positivity, ordered
eigenvalue summability, injectivity, and the full singular-value
representation remain further targets.

## F. What must be audited before marking V007 completed

1. Kernel-certified Gaussian-plane monomial orthogonality, angular
   Parseval for all radii, and isometric surjectivity (F2)–(F5).
2. Basis-independent Hilbert–Schmidt class and two-sided ideal,
   with (H2)–(H5).
3. Trace-class/nuclear-ideal equivalence and trace (T1)–(T2).
4. Density (M1), all ultraspherical moments (U1) and
   gamma-normalized regularized hypergeometric identity (U5).
5. Mathlib compact spectral eigenspaces, eigenvalue reality,
   nonnegativity, spectral completeness; stronger assertions
   separately as their dependencies are proved.

**No merge into main; no changes to V097.**
