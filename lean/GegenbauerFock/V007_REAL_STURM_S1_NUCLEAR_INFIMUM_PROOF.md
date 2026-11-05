# V007 — real Schatten–S₁ norm of the closed Sturm resolvent: proof and Lean obligations

**Status 2026-11-03 — EXACT REAL PROJECTIVE NUCLEAR NORM KERNEL-CERTIFIED.** The genuine real closed Sturm resolvent admits a positive operator-norm convergent nuclear expansion (CI #41440898371); its specific mass equals the spectral trace (CI #41441020071); general real nuclear rank-one membership (CI #41496631031) and the projective nuclear infimum upper bound (CI #41497090311) are certified. Most importantly, the **reverse bound for every admissible real rank-one expansion and the exact universal infimum identity** are kernel-certified by CI #41500000883 (9,108 jobs), module `UltrasphericalSturmLiouvilleResolventRealNuclearDualLower.lean`, `#print axioms` restricted to `propext`, `Classical.choice`, `Quot.sound`. This is a real projective nuclear-class certificate; a separate abstract complex CFC/Physlib trace-class identification has not been asserted.

This dossier records the now **kernel-certified** reverse bound, which requires all-representation finite-trace duality and cannot be inferred merely from one positive expansion. It distinguishes the real projective nuclear norm from the separate complex CFC/Physlib trace norm.

## Definitions

Let (H) be a complete separable real Hilbert space and let (T:H\to H) be bounded. An admissible nuclear expansion is

\[
T=\sum_{k=0}^{\infty}\beta_k (u_k\otimes v_k),
\qquad
\sum_{k=0}^{\infty}|\beta_k|\,\|u_k\|\,\|v_k\|<\infty,
\]

with operator-norm convergence, where
\((u\otimes v)x=\langle v,x\rangle u\).
Define its **projective nuclear norm**

\[
\|T\|_{\mathcal N}
=\inf\left\{
\sum_{k\ge0}|\beta_k|\,\|u_k\|\,\|v_k\|:
T=\sum_{k\ge0}\beta_k(u_k\otimes v_k)
\right\}.
\]

This is the standard (\mathcal S_1\) norm for real Hilbert-space operators when one invokes (or proves) the general equivalence between nuclear and Schatten trace classes. **Within the pinned Lean development**, the projective infimum is defined explicitly, and that equivalence remains a separate formal theorem. A single mass identity for one decomposition is not itself an infimum identity.

## Specific resolvent and upper bound

For (\lambda,t>0\), the genuine closed real Sturm resolvent (R_t) on
\(H=L^2(\nu_\lambda;\mathbb R)\) has the *certified* norm-convergent expansion

\[
R_t=\sum_{n\ge0}\rho_n P_n,\qquad
P_n=e_n\otimes e_n,\qquad
\rho_n=\frac{1}{t+n(n+2\lambda)}>0,
\]

where the Gegenbauer family \((e_n)\) is a complete orthonormal Hilbert basis and
\(\sum_n\rho_n<\infty\). Each \(P_n\) has operator norm one, so

\[
\|R_t\|_{\mathcal N}\le\sum_{n\ge0}\rho_n
=\operatorname{Tr}(R_t).
\]

The Lean module `UltrasphericalSturmLiouvilleResolventRealNuclearNorm.lean` defines the infimum over **all** admissible rank-one series and certifies its upper bound, not just the cost of the displayed series.

## Certified reverse inequality (finite-rank trace duality)

Fix any admissible expansion
\(T=\sum_k\beta_k(u_k\otimes v_k)\).
Let

\[
Q_N=\sum_{n=0}^{N-1}P_n
\]

be the orthogonal projection onto the first (N) Gegenbauer modes. For (N\ge1\), \(\|Q_N\|=1\). Evaluate its finite trace on a general rank-one term:

\[
\begin{aligned}
\sum_{n<N}\langle e_n,
 (u_k\otimes v_k)e_n\rangle
 &=\sum_{n<N}\langle e_n,v_k\rangle\langle e_n,u_k\rangle\\
 &=\langle Q_Nv_k,u_k\rangle.
\end{aligned}
\]

The Cauchy–Schwarz inequality and contractivity of (Q_N) imply

\[
\left|\langle Q_Nv_k,u_k\rangle\right|
\le\|u_k\|\,\|v_k\|.
\]

Because each finite trace functional is continuous in operator norm, we may evaluate the norm-convergent nuclear series termwise. This yields

\[
\left|
\sum_{n<N}\langle e_n,T e_n\rangle
\right|
\le\sum_k|\beta_k|\,\|u_k\|\,\|v_k\|.
\]

For (T=R_t\), the left side equals
\(\sum_{n<N}\rho_n\ge0\). Consequently, for **every** admissible nuclear expansion,

\[
\sum_{n<N}\rho_n
\le \sum_k|\beta_k|\,\|u_k\|\,\|v_k\|.
\]

Take (N\to\infty\), then the infimum over all representations. The universal lower bound follows:

\[
\operatorname{Tr}(R_t)=\sum_{n\ge0}\rho_n
\le\|R_t\|_{\mathcal N}.
\]

Combined with the upper bound,

\[
\boxed{\displaystyle
\|R_t\|_{\mathcal S_1(\mathbb R)}
=\|R_t\|_{\mathcal N}
=\sum_{n=0}^{\infty}
\frac1{t+n(n+2\lambda)}.}
\]

The equality is established **mathematically and in Lean 4**: the `RealNuclearDualLower.lean` module compiles successfully in CI #41500000883, with a clean axiom audit. The following list documents the discharged proof obligations.

## Discharged Lean obligations

1. Define the finite-coordinate orthogonal projection (Q_N) using the already certified Hilbert basis, or reuse the existing finite modal projection (NOT the resolvent truncation \(\sum_{n<N}\rho_nP_n\)).
2. Prove \(\|Q_Nv\|\le\|v\|\), and the finite trace identity
   `∑ n ∈ Finset.range N, inner ℝ (b n) (rankOne ℝ u v (b n)) = inner ℝ (Q_N v) u`.
3. Prove finite-trace evaluation commutes with the absolutely summable operator series, by continuity of each evaluation and `ContinuousLinearMap.map_tsum` or via finite sums of continuous linear maps.
4. Derive the **uniform** (in (N)) bound of each finite trace by the mass of every admissible rank-one expansion. The coefficient (1), not (N), is essential.
5. Use the certified resolvent diagonal and spectral trace summability to pass (N\to\infty\).
6. Apply the universal property of `sInf` to obtain the missing reverse bound; combine it with `sturmRealClosedResolvent_nuclearInfimum_le_spectralTrace`.
7. Audit all new declarations with `#print axioms`; reject `sorryAx` and `Lean.ofReduceBool`. Do not substitute a conditional hypothesis for obligation 4.

**Certified theorem names:** `realHilbertFiniteTraceCLM_apply`, `realHilbertFiniteTrace_abs_le_nuclearCost`, `sturmRealClosedResolvent_spectralTrace_le_allNuclearCosts`, and `sturmRealClosedResolvent_nuclearInfimum_eq_spectralTrace`. A previously failing experimental finite-sum module and a duplicate exact-infimum module were corrected on 2026-11-03; their standalone CI status is independent from the already successful main theorem.

No merge to `main` or edits to V097/V170. The PR remains Draft.
