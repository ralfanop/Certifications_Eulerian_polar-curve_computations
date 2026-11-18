# M15 §6.5 — finite algebraic bridge for the squarefree Fredholm determinant

Scope: finite-dimensional algebra, valid for any finite set of **distinct** positive integers. This note is a proof at the mathematical level, **not** a Lean compilation, FLINT/Arb certificate, or an identification of the geometric operator in the manuscript. It introduces no numerical approximations.

Let F be a finite subset of the positive integers, s a positive integer, and let a_n=1/n^s in ℚ (or ℂ). On the free module with basis indexed by F define the diagonal endomorphism T_F(e_n)=a_n e_n. Put P_F(z)=det(I+zT_F).

**Finite determinant theorem.** For all z, P_F(z)=∏_{n∈F}(1+za_n). This follows from the determinant of a diagonal matrix, with no convergence or trace-class assumption. In particular P_F(0)=1 and its degree is |F|.

**Coefficient theorem.** For every k, the coefficient of z^k is Σ_{A⊆F, |A|=k}∏_{n∈A}a_n. In particular the coefficient of z is Σ_{n∈F}a_n=Tr(T_F). This is the elementary-symmetric expansion of the product, and remains valid over ℚ.

**Power-trace theorem.** For each positive integer m, Tr(T_F^m)=Σ_{n∈F}a_n^m. As a formal power series over ℚ,

log(P_F(z))=Σ_{m≥1}(-1)^(m+1) z^m Tr(T_F^m)/m.

This is a *formal* identity in ℚ⟦z⟧, obtained by the formal logarithm of factors with constant term 1. No analytic branch or convergence is involved. Equivalently the logarithmic derivative satisfies

P_F'(z)/P_F(z)=Σ_{n∈F} a_n/(1+za_n)

in ℚ(z), and the coefficient of z^(m−1) in its Taylor series is (−1)^(m−1)Tr(T_F^m).

**Exact zero factorization.** If F consists of distinct positive integers, each zero −n^s (n∈F) is simple. Indeed, P_F'(−n^s)=a_n ∏_{j∈F,j≠n}(1−(n/j)^s) ≠ 0, since n^s≠j^s for distinct positive integers.

**Lean implementation boundaries.** First prove the finite determinant and trace identities for a finite diagonal matrix using `Matrix.det_diagonal` (or the corresponding available Mathlib theorem), `Matrix.trace`, and `Finset.prod`/`Finset.sum`. The exact theorem names and imports must be checked against the pinned Mathlib version before committing a Lean module. Next prove the coefficient and derivative identities algebraically. Only then pass to the infinite squarefree set with separate summability, product convergence and operator identification. Do not promote the finite statements to infinite Fredholm or zeta-regularized claims.

The finite formulas are exact rational identities: no relative-bit precision is meaningful or claimed. No changes to manuscripts, figures, or protected files; no merge.
