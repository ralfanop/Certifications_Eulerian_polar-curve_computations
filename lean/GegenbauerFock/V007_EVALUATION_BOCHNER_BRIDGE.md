# V007 — Evaluation/Bochner identification: exact proof obligations

**26 October 2026.** A mathematical proof and formalization plan,
NOT a kernel-checked Lean theorem. This concerns V007 only.
V097 is approved and unchanged; PR #16 must remain draft and unmerged.

## Object of the missing theorem

Assume λ>0, α>0, and μ=ν_λ, the actual Beta-pushforward
probability measure, concentrated on [-1,1]. For each complex z,
the desired equality of bounded complex-linear maps on L²(μ) is

\[
  \operatorname{ev}_{\alpha,z}\circ C_{\lambda,\alpha}
  =\operatorname{fourierFunctional}_{\lambda,z},
  \qquad
  (\operatorname{fourierFunctional}_{\lambda,z}f)
     =\int f(u)e^{izu/2}\,d\mu(u).                 \tag{B1}
\]

The existing Lean module EvaluationComposite.lean proves a convergent
weighted-moment series for the left side; UltrasphericalMeasure.lean
proves the actual integral representation of the right side. **The
identification (B1) itself is not yet in Lean.**

## Algebra of normalized coefficients

Put c=1/(4α). In the concrete Hilbert coefficient model,

\[
  (Cf)_n
  =\sqrt{\frac{c^n}{n!}}\,i^n\int u^n f(u)\,d\mu(u),
  \quad
  k_{\alpha,z}(n)=\sqrt{\frac{\alpha^n}{n!}}\,
                       \overline z^{\,n}.
\]

Mathlib's complex inner product is conjugate-linear in its first
argument. The n-th term of the point evaluation is consequently

\[
  \overline{k_{\alpha,z}(n)}(Cf)_n
  =\frac{(iz/2)^n}{n!}\int u^n f(u)\,d\mu(u).
                                                        \tag{B2}
\]

To formalize this equality, reduce the positive real square-root
factors using α>0 and the positivity of n!. **The phase is i^n,
not (-i)^n.** The sign flips only on conjugating coefficients to
compute the adjoint.

## Scalar Bochner/Fubini interchange

Choose any measurable representative of f. Probability normalization
and Cauchy–Schwarz imply

\[
  \int |f|\,d\mu\le\|f\|_{L^2(\mu)}<\infty.       \tag{B3}
\]

For each n define the complex-valued integrable section

\[
  g_n(u)=f(u)\frac{(izu/2)^n}{n!}.
\]

Since |u|≤1 for μ-a.e. u, the sum of L¹ norms satisfies

\[
  \sum_{n\ge0}\int|g_n(u)|\,d\mu(u)
  \le\sum_{n\ge0}\frac{(|z|/2)^n}{n!}\int|f|\,d\mu
  = e^{|z|/2}\int|f|\,d\mu <\infty.             \tag{B4}
\]

In particular a countable Bochner integral/series interchange is
justified, with no restriction that z be real:

\[
\begin{aligned}
  \sum_{n\ge0}\int g_n(u)\,d\mu(u)
  &=\int\sum_{n\ge0}g_n(u)\,d\mu(u)\\
  &=\int f(u)e^{izu/2}\,d\mu(u).                 \tag{B5}
\end{aligned}
\]

Combine (B2) with (B5) and then the already kernel-checked
weighted-series expression to get (B1). This proof applies to
general L² equivalence classes, not just smooth input functions.

## Pointwise bound and explicit analytic adjoint

The previously verified Fock evaluation norm and C operator bound
give, for every z∈ℂ,

\[
 |\operatorname{ev}_{\alpha,z}(Cf)|
 \le e^{\alpha|z|^2/2+1/(8\alpha)}\|f\|_2.     \tag{B6}
\]

The coefficient reconstruction, initially only a formal expression,

\[
 \mathscr R_\alpha F(z)
   =\sum_{n\ge0}F_n\sqrt{\alpha^n/n!}\,z^n,
\]

converges locally uniformly on ℂ by Cauchy–Schwarz, using the
Gaussian coherent-vector squared norm e^{α|z|²}. It therefore
defines an entire function. Its identification with the full
Gaussian-integrable Bargmann–Fock Hilbert space is a separate
isometry/completeness obligation.

With the same conjugate-first convention the desired analytic
adjoint identity is

\[
  (C^*F)(u)
  =\mathscr R_\alpha F(-iu/(2\alpha))
  \quad\text{for μ-a.e. }u.                    \tag{B7}
\]

The **minus sign** is fixed by the conjugation on (Cf)_n:
\[
 \langle Cf,F\rangle_{\ell^2}
 =\int\overline{f(u)}
    \mathscr R_\alpha F(-iu/(2\alpha))\,d\mu(u).
\]
Proving (B7) in Lean additionally requires the genuine L² class
of the right-hand side, the series/integral interchange and Riesz
adjoint uniqueness. Only then can one derive the integral Gram kernel

\[
  (C^*Cf)(u)=\int e^{uv/(4\alpha)}f(v)\,d\mu(v). \tag{B8}
\]

## Lean verification checklist

1. Prove the positive square-root/factorial identity (B2) for all n.
2. Establish the L¹ bound (B3) on actual L² representatives.
3. Prove integrability and summability (B4) for complex g_n.
4. Apply the Mathlib Bochner series/integral theorem to obtain (B5).
5. Use complex exponential series and functional extensionality for
   exact equality (B1) of the two bounded maps.
6. Construct the entire reconstruction and prove (B7), including
   the bounded L² restriction and correct signs.
7. Prove (B8), its trace-class interpretation and the later
   hypergeometric identity using independently certified moments.

Until each specific declaration compiles at the exact CI SHA and
its axiom audit is clean, it is a mathematical proof obligation,
not a Lean-certified conclusion. No sorry, admit or new axioms.
