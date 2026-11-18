# M15 §6.5 — exact zeros and multiplicities of the squarefree Fredholm determinant

Supplement to PR #372. This is an **analytic proof note**, not a Lean 4 compilation or a FLINT/Arb certificate. No claim about the manuscript's geometric operator or a zeta-regularized determinant is made.

Fix a real s>1 and let Q be the set of positive squarefree integers. Put
D_s(z)=∏_{n∈Q}(1+z n^{-s}).
As established in the preceding trace-class note, this product converges normally on compact subsets of the complex plane.

**Theorem.** The complete zero set of D_s is {−m^s:m∈Q}; every zero is simple. For each m∈Q,
D_s'(−m^s)=m^{-s}∏_{n∈Q,n≠m}(1−(m/n)^s) ≠ 0.
Consequently D_s has no zeros in the open disk |z|<1, and its Taylor logarithm at zero has radius of convergence exactly 1.

**Proof.** For fixed m, factor the m-th factor:
D_s(z)=(1+z m^{-s}) E_{s,m}(z),
where E_{s,m}(z)=∏_{n∈Q,n≠m}(1+z n^{-s}).
The remaining product converges normally. Its value at z=−m^s is nonzero: finitely many n<m yield nonzero factors; for n>m, the factors 1−(m/n)^s are strictly positive and the sum of their deviations from 1 is bounded by m^s Σ_{n>m}n^{-s}<∞. The standard infinite-product nonvanishing criterion applies to the tail. Differentiating the factorization gives the stated nonzero derivative.

Conversely, let z avoid all points −n^s. The factors with n^s≤2|z| are finite and nonzero. On the remaining tail, |z|n^{-s}<1/2 and Σ |z|n^{-s}<∞, so the tail product converges to a nonzero limit. Hence D_s(z)≠0. Since 1∈Q, z=−1 is a simple zero, and the analytic logarithm at zero cannot extend holomorphically across it; the series radius is precisely 1.

**Remaining formal obligations.** Mathlib construction of the diagonal trace-class operator, its determinant/product identification, nonvanishing of summable infinite products, differentiation after extraction of a factor, and the exact squarefree Dirichlet identity. This note does not discharge any of those Lean obligations. It contains no numerical claims requiring the 3,600,000-bit standard.

No protected source, figure, manuscript, V007 or V097 modification; no merge.
