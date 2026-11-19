# M16.6 §13: exact scalar fourth-power spectral sum

**Scope:** analytic identity for the explicitly defined scalar model only. No Lean compilation, Arb certificate, operator Schatten theorem or det4 claim.

For integers L >= 2 define A(L) = sum over k in Z excluding 0 and -L of 1/[4|k||k+L|]^4.

The rational partial fraction identity (x != 0,-L) is

1/[x^4(x+L)^4] = (x^-4+(x+L)^-4)/L^4 + 4((x+L)^-3-x^-3)/L^5 + 10(x^-2+(x+L)^-2)/L^6 + 20((x+L)^-1-x^-1)/L^7.

Each displayed *paired* summand has an absolutely convergent sum over the admissible integers; do not separate the two first-power harmonic sums.

The four integer sums of the parenthesized terms are respectively
4 zeta(4)-2/L^4, -2/L^3, 4 zeta(2)-2/L^2, -2/L.
Multiplying by 1/4^4 yields

A(L) = zeta(4)/(64 L^4) + 5 zeta(2)/(32 L^6) - 35/(128 L^8).

For the positive convergent weighted sum S4 = sum_{L>=2} 2(L^2-1) A(L), absolute convergence follows from A(L)=O(L^-4). The outer summation gives

S4 = (zeta(4)/32)(zeta(2)-zeta(4)) + (5 zeta(2)/16)(zeta(4)-zeta(6)) - (35/64)(zeta(6)-zeta(8))
   = pi^6/17280 - pi^8/907200.

This is an exact analytic scalar identity, NOT an FLINT/Arb certificate. Before transferring it to M16.6: check the frozen source index set, multiplicity and labels; formalize partial fractions and summability in Lean with an axiom audit; run CI on exact HEAD; use ctx.prec=3600000 and individual rel_accuracy_bits() >= 3400000 assertions for nonzero quantities; and certify that the exact Arb interval endpoints fall strictly in one rounding cell at 1,000,001 significant decimal digits. A scalar model does not prove general operator det4.
