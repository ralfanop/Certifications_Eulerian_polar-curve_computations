# Shared diagonal det4: explicit fourth-order Taylor remainder and zero-free disk

Scope: analytic supplement to Draft #376 (and model #373). This is NOT a Lean 4 certificate, an Arb certificate, or an identification with a manuscript-specific physical operator. No manuscript/figure edits.

Let lambda_n=1/(n+2), m_n=(n+1)(n+2), and M(q)=sum_{n>=0} m_n lambda_n^q for integers q>=4. Set A=M(4)=zeta(2)-zeta(3)>0. Let D4 be the normally convergent regularized product from Draft #373, and let L(z) be the unique analytic logarithm with L(0)=0 on |z|<2.

**Explicit remainder theorem.** For every complex z with |z|<=r<2,

    |L(z)+A*z^4/4| <= A*r^5 / [10*(1-r/2)].

Indeed, for q>=4, lambda_n^(q-4)<=2^(-(q-4)), so M(q)<=2^(-(q-4))*A. The absolutely convergent logarithmic series gives

    L(z)+A*z^4/4 = sum_{q>=5} (-1)^(q+1) M(q)*z^q/q.

Since 1/q<=1/5 for q>=5, its absolute value is bounded by

    (A/5)*sum_{q>=5} 2^(-(q-4))*r^q
      = A*r^5/[10*(1-r/2)].

This is a strict analytic bound for r<2, not a numerical ball certificate. It also gives a reproducible truncation bound: for every integer N>=4,

    |L(z)-sum_{q=4}^N (-1)^(q+1) M(q)*z^q/q|
      <= A*r^(N+1)*2^(-(N-3))/[(N+1)*(1-r/2)].

The proof uses 1/q<=1/(N+1) and a geometric series. This bound is uniform on the closed disk |z|<=r.

**Determinant-level bound.** Put P(z)=-A*z^4/4 and E(r)=A*r^5/[10*(1-r/2)]. Then

    |D4(z)-exp(P(z))| <= exp(A*r^4/4)*(exp(E(r))-1).

This follows from D4=exp(P+R), |R|<=E(r), and |exp(R)-1|<=exp(|R|)-1. In particular the order-four Taylor coefficient of D4 is -A/4, and all lower nonconstant Taylor coefficients vanish.

**Zero-free disk and sharp radius.** The regularized exponential factor never vanishes; the product factors have zeros at z=-(n+2), with multiplicity m_n. For |z|<2, each factor is nonzero and the absolutely convergent logarithm L shows D4(z)=exp(L(z)) is nonzero. The n=0 factor has a zero at z=-2 of multiplicity m_0=2; the product of all other factors is nonzero there because their logarithmic regularization is absolutely summable. Therefore the Taylor series of L at zero has radius exactly 2 (it cannot extend holomorphically across a zero of D4 while remaining a logarithm).

**Certification scope.** These are classical consequences of normally convergent canonical products and absolutely convergent power series, not asserted as novel. For Lean: formalize summability and the geometric majorants before identifying a Hilbert-space operator trace. For Arb: evaluate A with ctx.prec=3600000, assert rel_accuracy_bits()>=3400000, then prove strict containment of the entire rigorous ball in one rounding cell at 1000001 significant decimal digits; do not infer that from the analytic bounds alone. No numeric certificate is claimed here.

Cross-reference: Drafts #373, #375, #376. No merge.