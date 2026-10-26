# V007 — Complete mathematical proofs: analytic adjoint and exponential Gram integral

**26 October 2026.** These are complete paper-level arguments, not a
claim of complete Lean certification. V097 remains immutable. GitHub
PR #16 remains a draft and must not be merged without author approval.

## Setup and conjugation convention

Fix λ>0 and α>0. Let μ=ν_λ be the actual ultraspherical probability
measure (the affine image of the symmetric Beta law), with support
in [-1,1], and put c=1/(4α). Mathlib uses inner products
conjugate-linear in their first argument:

\[
\langle f,g\rangle_{L^2}=\int\overline{f(u)}g(u)\,d\mu(u),
\qquad
\langle x,y\rangle_{\ell^2}=\sum_{n\ge0}\overline{x_n}y_n.
\]

The actual bounded coefficient operator is

\[
 (Cf)_n=\gamma_n\int u^n f(u)\,d\mu(u),
 \quad
 \gamma_n=i^n\sqrt{\frac{c^n}{n!}}.              \tag{1}
\]

For any F=(F_n)∈ℓ², its Fock reconstruction is

\[
 \mathcal R_\alpha F(z)
 =\sum_{n=0}^{\infty}F_n
    \sqrt{\frac{\alpha^n}{n!}}z^n.               \tag{2}
\]

By Cauchy–Schwarz, its series is locally uniformly absolutely
convergent. The same estimate gives

\[
 |\mathcal R_\alpha F(z)|
 \le \|F\|_{\ell^2}\exp(\alpha|z|^2/2).          \tag{3}
\]

Thus it defines an entire function. Identifying the resulting
coefficient Hilbert space with the full Gaussian-area Bargmann–Fock
realization remains a separate Lean isometry theorem.

## Analytic adjoint for arbitrary coefficients

**Theorem.** For every F∈ℓ², the actual Hilbert adjoint satisfies

\[
 \boxed{(C^*F)(u)=
 \mathcal R_\alpha F\!\left(-\frac{iu}{2\alpha}\right)}
 \qquad\text{for μ-a.e. }u.                     \tag{4}
\]

**Proof.** Since |u|≤1 μ-almost everywhere, (3) yields

\[
 \left|\mathcal R_\alpha F(-iu/(2\alpha))\right|
 \le e^{1/(8\alpha)}\|F\|_{\ell^2}.             \tag{5}
\]

The restriction of an entire function to the imaginary line is
continuous, so the right-hand side is measurable and (5) proves
membership in L²(μ), including the bound
\(\|\mathcal R_\alpha F(-i(\cdot)/(2\alpha))\|_2
\le e^{1/(8\alpha)}\|F\|_{\ell^2}\).

Using (2), for |u|≤1,

\[
 \mathcal R_\alpha F(-iu/(2\alpha))
 =\sum_{n\ge0}\overline{\gamma_n}F_n u^n.
                                                        \tag{6}
\]

This series converges absolutely **uniformly** on [-1,1], because

\[
 \sum_n|\overline{\gamma_n}F_nu^n|
 \le\|F\|_{\ell^2}
    \left(\sum_n\frac{c^n}{n!}\right)^{1/2}
 =e^{c/2}\|F\|_{\ell^2}.                       \tag{7}
\]

For f∈L²(μ) we have \(\|f\|_1\le\|f\|_2\), since μ is a
probability measure. Bound (7), multiplied by |f(u)| and integrated,
justifies the infinite-series/integral interchange. Hence

\[
\begin{aligned}
\langle f,\mathcal R_\alpha F(-i(\cdot)/(2\alpha))\rangle
 &=\sum_{n\ge0}\overline{\gamma_n}F_n
      \int\overline{f(u)}u^n\,d\mu(u)\\
 &=\sum_{n\ge0}\overline{(Cf)_n}F_n
 =\langle Cf,F\rangle.
\end{aligned}                                                   \tag{8}
\]

The defining Hilbert-adjoint identity and Riesz uniqueness establish
(4). This also proves that (6) is an L² identity, not simply a
formal power series. The negative sign in the evaluation argument
is essential.

## Genuine exponential Gram integral

Let S=C* C be the bounded Gram operator and let
\(K_c(u,v)=\exp(cuv)\). From (4) and the already verified equality
of Fock evaluation with the Eulerian Bochner integral at **every**
complex z, set z=-iu/(2α). Then, for μ-almost every u,

\[
 \boxed{
 (Sf)(u)=\int_{-1}^{1}
       e^{uv/(4\alpha)}f(v)\,d\mu(v).}
                                                        \tag{9}
\]

This is a genuine scalar Bochner integral. On [-1,1]²,
\(0<K_c(u,v)\le e^c\), so its integrand belongs to L¹ for
every f∈L² and almost every u. Furthermore,

\[
 \|Sf\|_{L^2}\le e^c\|f\|_{L^2}.               \tag{10}
\]

The kernel is real, symmetric, and measurable. For f,g∈L²,
Fubini is valid since
\(\int\!\!\int |g(u)f(v)|K_c(u,v)\,d\mu(v)d\mu(u)
 \le e^c\|g\|_2\|f\|_2\). Thus

\[
 \langle g,Sf\rangle=
 \int\!\!\int \overline{g(u)}e^{cuv}f(v)
      \,d\mu(v)d\mu(u).                         \tag{11}
\]

The resulting Gram form is positive and selfadjoint and has the
absolutely convergent rank-one expansion

\[
 \langle f,Sf\rangle
 =\|Cf\|_{\ell^2}^2
 =\sum_{n\ge0}\frac{c^n}{n!}
   \left|\int u^n f(u)\,d\mu(u)\right|^2.
                                                        \tag{12}
\]

The kernel is square-integrable on μ⊗μ, and S is compact.
Since C has summable squared row norms, C is Hilbert–Schmidt,
hence S=C*C is trace class and

\[
 \operatorname{tr}(S)=\|C\|_{\rm HS}^2
 =\int e^{u^2/(4\alpha)}\,d\mu(u).             \tag{13}
\]

The last equality has a Lean certificate for the **coefficient-row
energy**; identifying that row energy with a separately formalized
Hilbert–Schmidt-ideal norm and trace remains a different task.

## Exact Lean certification boundary

- The V007 branch already has a fully compiled all-complex-frequency
  Fock-evaluation/Bochner identity.
- AnalyticAdjoint.lean gives the real Hilbert adjoint on coherent vectors,
  and the norm-convergent adjoint row expansion for arbitrary F∈ℓ².
- GramKernelSeries.lean gives the exact norm-convergent Gram expansion
  and full sesquilinear coefficient pairing.
- GramIntegralKernel.lean identifies the imaginary-axis Fock evaluation
  with the integral of the real exponential kernel **only if its exact
  SHA and associated workflow have passed**.
- The Lean equality of (4) as an equality of actual L² classes,
  and consequently of (9) as an equality of the Gram operator and
  the displayed integral operator, are **not yet kernel-certified**.

Further Lean tasks: construct measurability and an L² bound for
the entire-function restriction; prove that its L² class equals
the norm-convergent series in (6); use adjoint uniqueness to
complete (4), then obtain (9) from the all-z kernel evaluation.
Every additional declaration needs compilation and an audit of
its precise axiom dependencies. No sorry/admit/new axioms; no
merge into main and no modification to V097.
