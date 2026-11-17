# M15 §6.5: differentiated squarefree trace-log (analytic subcase)

Supplement to PR #372. **Not a Lean proof, Arb certificate, or identification of the geometric operator.**

Fix s>1 and Q={positive squarefree integers}. For D_s(z)=∏_{n∈Q}(1+zn^{-s}), the analytic logarithm L_s(0)=0 exists on |z|<1. Normal convergence and the geometric series yield

L_s'(z)=D_s'(z)/D_s(z)=Σ_{n∈Q}1/(n^s+z)
=Σ_{k≥0}(-z)^k ζ((k+1)s)/ζ(2(k+1)s).

Proof: for |z|≤r<1 the absolute geometric majorant is n^{-s}/(1-r), whose sum is finite. Hence differentiation and summation commute. In particular, for m≥1,

L_s^(m)(0)=(-1)^(m-1)(m-1)! ζ(ms)/ζ(2ms).

For |z|≤r<1 and K≥0 the remainder after k=K is bounded by ζ(s)r^(K+1)/(1-r).

Let L_{s,N}(z)=Σ_{n∈Q,n≤N}log(1+zn^{-s}). The integral test and |log(1+w)|≤|w|/(1-|w|) imply, for N≥1 and |z|≤r<1,

|L_s(z)-L_{s,N}(z)|≤[r/(1-r)]N^(1-s)/(s-1),

|L_s'(z)-L_{s,N}'(z)|≤[1/(1-r)]N^(1-s)/(s-1).

The derivative bound follows from |n^s+z|≥n^s(1-r). These give independent spectral and power-series truncation controls. They are **not** 3600000-bit numerical certificates. Lean obligations remain the finite spectral derivative, summability, derivative exchange, and squarefree Dirichlet identity. No sorry or axioms introduced.