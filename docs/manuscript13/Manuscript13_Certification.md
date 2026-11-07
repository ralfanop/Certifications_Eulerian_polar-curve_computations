# Manuscript 13: Lean 4 and Arb certification record

*Eulerian Fourier profiles and Gegenbauer–Fock operators: dimensional and spectral bridges*. Roberto Alfano, 7 November 2026. A PDF version of this record is [Manuscript13_Certification.pdf](Manuscript13_Certification.pdf).

## 1. Scope.

This record states, for manuscript 13, what is kernel-checked in Lean 4 and which numerical values are certified in exact rational and Arb ball arithmetic. It replaces Appendix B (Lean 4 certification) of the article and the description of the certificates formerly given in its Code Availability statement. Equation, section and result numbers are those of the version of 2 November 2026 with the notation correction of 5 November 2026, in which the Hilbert spaces are written $\mathcal H_\lambda$.

## 2. The Lean 4 library.

The library `GegenbauerFock`, in the directory `lean/GegenbauerFock` of the repository <https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations> on the branch [`gegenbauer-fock-formalization-20261025`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/tree/gegenbauer-fock-formalization-20261025), is compiled with the Lean 4 toolchain `v4.35.0-rc3` and Mathlib commit `0272bbe1c093`. On 2 November 2026 (commit [`11320490`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/tree/1132049025418c06f8b6f16a8e0112ab3088c4ba)) its 792 modules contained 2547 theorems and lemmas. Continuous integration recompiles the modules below from source and prints the axioms of their main statements; the audit found only `propext`, `Classical.choice` and `Quot.sound`, and no `sorry`, `admit`, added axiom or `native_decide`.

Every numbered statement of the article is formalised:

- Definition 2.1 and Proposition 3.1 in `Manuscript13Measure`;

- Proposition 3.2 by the identification of the image of the beta law under $u=2x-1$ with $\nu_\lambda$;

- Propositions 3.3, 3.4 and 3.6 in `Section3Ultraspherical`;

- Section 4 and Table 1 in `Section4Resolvent`;

- Proposition 5.1 and Corollary 5.2 in the Sturm–Liouville modules;

- Definition 6.1 and Theorems 6.2–6.4 in the ultraspherical Fock modules and `Section6Corollaries`;

- Propositions 6.5 and 6.6 in `Section6Corollaries` and `EulerianStateShi`;

- Section 7 in `Section7Intertwining` and `Section7Closed`;

- Theorem 8.1, Propositions 8.2 and 9.1 and Lemma 9.2 in `Section8Section9`;

- Proposition 10.1 and the identities of Section 10 in `Section10Comparison`.

## 3. Classical inputs.

Classical inputs enter as explicit hypotheses and are not results of the article: the reality of the Neumann function $Y_\nu$ and the closed form of $Y_{1/2}$, used only for the complete kernels of Section 4, the zonal marginal law behind (38), and the Funk–Hecke formula behind Proposition 10.1. The closed forms of $J_{\pm1/2}$ are proved.

## 4. Formalisation conventions.

Mathlib has no singular values, Schatten classes or continuous-spectrum predicate, so (72) is formalised as the existence of an operator of rank at most $N$ within $\exp(c/2)(c^N/N!)^{1/2}$ of $C_{\lambda,\alpha}$ in operator norm, Schatten membership as the summability of these bounds raised to every power $p>0$, and the last clause of Proposition 8.2 as $\ker S_{\lambda,c}=\{0\}$ with dense range and without surjectivity. The complex operator $D_\lambda$ of Theorem 7.3 is the complexification of the real selfadjoint realisation of the library, and the values at $\rho=0$ in Section 4 are stated as limits.

## 5. Numerical certificates.

The script [`numerics/arb/v007_arb.py`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/main/numerics/arb/v007_arb.py), with its log `v007_arb.log`, uses exact rational arithmetic and Arb balls at 256 bits (`python-flint`); every comparison is exact or a certain Arb comparison. It certifies: for Proposition 6.5, the fifteen-term partial sum of $I=\sum_n1/[4^nn!(2n+1)]$, its remainder bound with $e^{1/4}<4/3$ and the printed decimal enclosure, and, independently, that $I=\sqrt\pi\operatorname{erfi}(1/2)$ lies inside that enclosure; for Table 1, $A_d(k)k^{d-2}=4\Gamma(d/2)(4\pi)^{(d-2)/2}$ for $d=3,\ldots,12$ and the endpoint values $2k$ ($d=1$) and $4$ ($d=2$), as exact rational multiples of powers of $\pi$; for Corollary 4.2, the factor $8\pi$; for Proposition 6.6 at $\alpha=1$, the agreement of $\sum_k1/[16^k(2k)!(2k+1)^2]$ with $4\operatorname{Shi}(1/4)$.

The directory [`figures/13_gegenbauer_fock`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/tree/main/figures/13_gegenbauer_fock) holds the sources, data and scripts of the figures, and the certificates of those whose captions state numerical facts. For Figure 4(b), `cert_fig3_gram.py` computes the normalised Gram matrix $\langle F_m,F_n\rangle/(\|F_m\|\|F_n\|)$, $0\leq m,n\leq11$, of $F_n=C_{1/2,\alpha}P_n$ with $\alpha=1/16$ ($c=4$) from exact rational partial sums up to $K=90$, with tail at most $55c^K/K!<6\cdot10^{-83}$, and certifies that the entries with $m+n$ odd vanish, that those with $m+n$ even are positive and decrease away from the diagonal, and that the largest off-diagonal entry, at $(m,n)=(0,2)$, is $0.753174039953$ to twelve digits. For Figure 5, `make_fig1_fig4_data.py` encloses the tail $\|C-C_N\|_{\mathrm{HS}}^2=\sum_{n\geq N}c^n/[(2n+1)n!]$ for $\lambda=1/2$, $\alpha\in\{1/4,1,4\}$ and $0\leq N\leq20$ by exact rational partial sums and a rigorous remainder, and checks the inequality $\|C-C_N\|_{\mathrm{HS}}^2\leq e^cc^N/N!$ of Theorem 8.1 exactly at all 63 points.
