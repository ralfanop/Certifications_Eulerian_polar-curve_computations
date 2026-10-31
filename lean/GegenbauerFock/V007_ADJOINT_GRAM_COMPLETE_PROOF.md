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

## Lean 4 formal certification — completed 26 October 2026

**The two infinite-dimensional L² operator identities (4) and (9) are
now fully kernel-checked in the concrete coefficient-space model.**

- **Certified code commit:** `444e3b80cd3e1241909ed51b5930812b1e160729`.
- **Exact-head GitHub Actions:** [run 40386146429](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40386146429), conclusion **SUCCESS**, with all compilation/regression steps and final axiom audit passing.
- **Kernel axiom dependencies:** every relevant declaration below has only
  `propext`, `Classical.choice`, `Quot.sound`.
  No `sorryAx` and no `Lean.ofReduceBool`.

### Formalized analytic adjoint

1. `FockAnalyticRestriction.restrictionCLM` in
   `AnalyticRestrictionCLM.lean` constructs a **genuine bounded
   ℂ-linear operator** from the infinite Fock coefficient Hilbert
   space ℓ² into the concrete ultraspherical L². Its action is the
   imaginary-axis coherent evaluation of any coefficient vector.
2. `FockAnalyticRestriction.evaluation_single_imaginary` and
   `FockAnalyticRestriction.restrictionLp_single` in
   `AnalyticAdjointComplete.lean` certify the exact weighted
   monomial basis restriction, including all complex phases.
3. `FockAnalyticRestriction.restrictionCLM_eq_C_adjoint` proves
   equality with **the actual adjoint of the concrete bounded
   Gegenbauer–Fock operator** by the Mathlib canonical-ℓ²-basis
   density theorem and continuity.
4. `FockAnalyticRestriction.adjoint_eq_analytic_restriction`
   specializes this equality to every F∈ℓ², as an equality of
   actual L² equivalence classes. This is identity (4), not
   merely an equality on finite-support coefficient sequences.

### Formalized integral Gram operator

1. `GeneralUltrasphericalFock.gramIntegralOperator` in
   `GramIntegralComplete.lean` is an actual bounded ℂ-linear
   operator L²(νλ)→L²(νλ), constructed from the verified
   imaginary-axis Fock restriction composed with C.
2. `gramIntegralOperator_apply` identifies its output for
   every f∈L² with the L² class of the actual complex Bochner
   integral of the real exponential kernel e^{uv/(4α)}.
3. `gram_eq_gramIntegralOperator` proves **operator equality**
   C†C=T, not only an equality of quadratic forms.
4. `gram_eq_integralLp` proves identity (9) as an equality
   in the concrete source L² for arbitrary f.

### Certification boundary that still remains

The above two operator identities are complete **for the concrete
ℓ² coefficient model**. The following are *separate, not yet
kernel-certified*, and must not be silently inferred from this result:

- the isometric equivalence to the full Gaussian-area holomorphic
  Bargmann–Fock Hilbert space, and the Lean holomorphy theorem for
  unrestricted reconstructed entire functions;
- the explicit Gamma-density equality and general ultraspherical
  moment/hypergeometric closed forms;
- a separately bundled Mathlib Hilbert–Schmidt-ideal or trace API,
  Schatten class and full spectral/injective/dense-range results;
- domain-aware Sturm–Liouville selfadjointness and kernel commutation;
- formal interval-arithmetic certifications for numerical claims
  where needed.

The previously certified finite-rank approximation, concrete
compactness, row-energy exponential-integral identity, all-complex-z
Bochner series interchange, and kernel evaluations remain unchanged.

**V007 only.** PR #16 remains Draft and unmerged. Approved V097 and
the repository main branch remain unchanged.
