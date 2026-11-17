# M16 v16.5 §14.5 — quantitative finite W1 bounds (independent analytic audit)

Source lock: author-approved ZIP SHA-256 `4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`. This note does not alter any manuscript source. It complements (does not duplicate) PR #341's W-infinity obstruction.

Let 0<q<1 and set C(q)=4(3-q)/(1-q)^3. On nonnegative integer indices define p_n=(1-q)q^n and r_n=4(n+1)(n+3)q^n/C(q). Push both laws forward by E_n=2n+1.

**Exact first moments.** Differentiating the absolutely convergent power series on 0<q<1,
E_p[n]=q/(1-q),
E_r[n]=q C'(q)/C(q)=q(3/(1-q)-1/(3-q)).
Thus the strictly positive mean gap is
Delta(q)=E_r[n]-E_p[n]=q(2/(1-q)-1/(3-q))=q(5-q)/((1-q)(3-q))>0.

**Quantitative transport bounds.** Kantorovich's inequality for the 1-Lipschitz observable f(E)=E gives the lower bound. The independent coupling, using |E_n-E_m|=2|n-m|<=2(n+m), gives the upper bound. Therefore
2q(5-q)/((1-q)(3-q)) <= W_1(p_E,r_E)
<= 2q(4/(1-q)-1/(3-q)).
Both bounds are finite and exact rational functions of q. They hold for all 0<q<1. In contrast, PR #341 proves W_infinity=+infinity by a separate tail argument. There is no contradiction: finite W1 does not imply bounded essential displacement.

**Obligations for Lean 4.** (1) geometric series and differentiated first-moment identity with absolute convergence; (2) positivity of Delta using q>0, 1-q>0, 3-q>0; (3) pushforward expectation under E_n=2n+1; (4) coupling-independent W1 lower bound via the 1-Lipschitz observable or direct triangle inequality; (5) existence of independent product coupling and integrability for upper bound. The rational identities can be isolated as ring/field_simp/nlinarith lemmas. None is represented here as Lean-verified.

**Numerical certification.** No floating-point constants or FLINT/Arb enclosures are asserted. The coefficients and symbolic rational identities are exact; no 3,600,000-bit computation is needed for them. The million-digit standard remains open for any subsequent nonrational numerical specializations.

**Scope.** These are probability/transport identities for a specified discrete model, not a Maxwell-field physical transport theorem.
