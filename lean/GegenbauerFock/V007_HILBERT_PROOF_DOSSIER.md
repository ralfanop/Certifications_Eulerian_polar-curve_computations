# V007 — Hilbert-space operator proof dossier (mathematical derivations; Lean status tracked separately)

**26 October 2026. Status: mathematical proof specification. NOT a kernel-checked Lean certification of the full operator theorems.**
V097 is not modified. No content from this file is to be merged into V097.
The code checked so far constructs the general probability measure as an affine image of a symmetric Beta distribution and certifies a scalar Bochner integral's algebraic rules. The following genuine Hilbert-space statements remain to be formalized.

## 1. The probability measure

For \(\lambda>0\), put \(a=\lambda+\tfrac12\).
Let \(X\sim\mathrm{Beta}(a,a)\) with density \(x^{a-1}(1-x)^{a-1}/B(a,a)\) on \((0,1)\). Set \(U=2X-1\). Then

\[
d\nu_\lambda(u)=
\frac{\Gamma(\lambda+1)}
{\sqrt\pi\,\Gamma(\lambda+\frac12)}
(1-u^2)^{\lambda-\frac12}\mathbf1_{(-1,1)}(u)\,du.
\]

The density formula follows by substitution \(x=(u+1)/2\), including the Jacobian \(dx=du/2\), and the Gamma duplication formula.
Its normalization is already inherited from Mathlib's \`ProbabilityTheory.isProbabilityMeasureBeta\` and its affine pushforward, certified in \`UltrasphericalMeasure.lean\`. **The identification of the displayed classical Gamma density with the pushforward is not yet in Lean.**

By a Beta integral, for all integers \(n\ge0\),

\[
m_{2n}=\int u^{2n}d\nu_\lambda(u)=
\frac{(\frac12)_n}{(\lambda+1)_n},\qquad
m_{2n+1}=0.
\]

Symmetry and Beta moments remain separate Lean obligations.

## 2. Segal–Bargmann reproducing-kernel Hilbert space

Fix \(\alpha>0\). Use \(\mathcal F_\alpha\), the holomorphic Bargmann–Fock space with Gaussian scalar product **linear in the first argument**,

\[
\langle F,G\rangle_{\mathcal F_\alpha}
=\frac{\alpha}{\pi}\int_{\mathbb C}
F(z)\overline{G(z)}e^{-\alpha|z|^2}\,dA(z).
\]

The reproducing kernel at \(w\) is \(k_w(z)=e^{\alpha z\overline w}\).
Let \(w_u=-iu/(2\alpha)\), and \(\kappa_u=k_{w_u}\). Then

\[
\kappa_u(z)=e^{izu/2},\qquad
\|\kappa_u\|_{\mathcal F_\alpha}^2
=e^{u^2/(4\alpha)}.
\]

Thus \(u\mapsto\kappa_u\) is strongly measurable and uniformly bounded on \([-1,1]\). **In Lean, the analytic holomorphic Fock Hilbert space (or its isometric \(\ell^2\) coefficient model) and these reproducing formulas still need construction.**

## 3. Bochner operator, boundedness and Hilbert–Schmidt identity

For \(f\in L^2(\nu_\lambda)\), define

\[
C_{\lambda,\alpha}f
=\int_{-1}^1 f(u)\kappa_u\,d\nu_\lambda(u)
\quad\in\mathcal F_\alpha.
\]

Since \(\nu_\lambda\) is a probability measure and \(\sup\|\kappa_u\|\le e^{1/(8\alpha)}\),
Cauchy–Schwarz gives Bochner integrability and the bounded estimate

\[
\|Cf\|\le e^{1/(8\alpha)}\|f\|_{L^2(\nu_\lambda)}.
\]

Using Parseval in \(\mathcal F_\alpha\), Tonelli and any orthonormal basis:

\[
\|C\|_{\mathrm{HS}}^2
=\int_{-1}^1\|\kappa_u\|^2\,d\nu_\lambda(u)
=\int_{-1}^1e^{u^2/(4\alpha)}\,d\nu_\lambda(u)
={}_1F_1\left(\frac12;\lambda+1;\frac1{4\alpha}\right).
\]

The last hypergeometric identity uses the even moments and monotone convergence of the nonnegative exponential series. **None of this full operator argument has yet been kernel-checked.** The \`BochnerStage.lean\` module only certifies scalar Bochner-integral rules with explicit integrability hypotheses.

## 4. Adjoint, Gram operator, trace and positivity

With the linear-first convention,

\[
(C_{\lambda,\alpha}^*F)(u)
=\langle F,\kappa_u\rangle_{\mathcal F_\alpha}
=F(-iu/(2\alpha))
\quad\text{for \(\nu_\lambda\)-almost every \(u\)}.
\]

In particular,

\[
(S_{\lambda,\alpha}f)(u):=(C^*Cf)(u)
=\int_{-1}^1e^{uv/(4\alpha)}f(v)\,d\nu_\lambda(v).
\]

The Gram operator is positive, selfadjoint, compact and trace class, with

\[
\operatorname{tr}S_{\lambda,\alpha}
=\|C\|_{\mathrm{HS}}^2.
\]

Formalizing the adjoint must use the **correct complex conjugations**. The formula is evaluation at \(-iu/(2\alpha)\), not evaluation at \(+iu/(2\alpha)\).

## 5. Explicit finite-rank approximation and Schatten decay

The normalized Bargmann–Fock monomials are

\[
e_n(z)=\sqrt{\frac{\alpha^n}{n!}}\,z^n.
\]

The \(e_n\)-coefficient of the coherent section \(\kappa_u\) is
\[
b_n(u)=\frac{(iu)^n}{2^n\alpha^{n/2}\sqrt{n!}}.
\]
Let \(P_N\) be the orthogonal projection onto \(\operatorname{span}\{e_0,\dots,e_{N-1}\}\), and \(C_N=P_N C\). Then \(C_N\) has rank at most \(N\), and with \(c=1/(4\alpha)\),

\[
\|C-C_N\|_{\mathrm{HS}}^2
=\sum_{n=N}^{\infty}\frac{c^n}{n!}\,m_{2n}
\le\sum_{n=N}^{\infty}\frac{c^n}{n!}
\le e^c\frac{c^N}{N!}.
\]

The final inequality follows from \(n!\ge N!(n-N)!\) for \(n\ge N\).
Consequently,

\[
s_{N+1}(C)\le \|C-C_N\|
\le e^{c/2}\,\frac{c^{N/2}}{\sqrt{N!}}.
\]

This establishes (at the mathematical level) compactness and membership in every Schatten class \(S_p\), \(p>0\), via factorial singular-value decay. **For Lean, formalize the orthonormal-basis/Fock identification, finite-rank truncation, tail bound, approximation-number inequality and Schatten summability separately.**

## 6. Unbounded Sturm–Liouville operators: a different obligation

The pointwise identity already kernel-checked,

\[
L_{\lambda,c}^{(u)}e^{cuv}=L_{\lambda,c}^{(v)}e^{cuv},
\]

is not a proof of the operator commutation \(\,L_{\lambda,c}S_c=S_cL_{\lambda,c}\).
The latter additionally needs the canonical selfadjoint realization, a weighted Green identity, vanishing endpoint terms on a dense core, regularity of the integral operator, and **domain invariance**.

These are outside the present Hilbert–Schmidt block. They are also outside V097; all new proof certificates belong to V007.

## 7. Verified versus pending

- **Verified in Lean:** Beta-pushforward probability measure, mass one, positivity of the underlying beta density, scalar-valued Bochner integral algebra and norm domination under integrability hypotheses, plus the earlier five modules.
- **Not yet verified in Lean:** classical Gamma density equality, general ultraspherical moments, concrete \(L^2\to\mathcal F_\alpha\) continuous operator, Hilbert–Schmidt norm, adjoint, Gram trace and compactness, Schatten estimates, unbounded-operator domains.
- **Numerical certificates:** not required for qualitative Hilbert-space assertions; numerical examples of \({}_1F_1\), singular values, or spectral gaps will require separately stated rational/interval bounds if included in V007.

Every Lean assertion added subsequently must be compiled using the repository's pinned toolchain and checked for \`sorryAx\`/\`Lean.ofReduceBool\` dependencies.