# M12 §9 — quartic critical-window asymptotic

Research extension of Theorem 9.6, based on the frozen 20 November 2026 manuscript.
This is a mathematical proof, not yet a kernel certificate of the analytic theorem.
No existing manuscript text or classical appendix is changed.

## Statement

For independent sums S_M,T_M of M uniform[-1/2,1/2] variables, let
N_M(c) = E exp(S_M T_M/(cM)). For fixed real λ put c_M = 1/12 + λ/√M.
Only sufficiently large M is needed, so c_M > 0. Then

    N_M(c_M)/M^(1/4) → F(λ)
    F(λ) = (1/(2√π)) ∫_R exp(-u^4/40 - 6λu²) du.

In particular F(0) = 40^(1/4) Γ(1/4)/(4√π), and
M^(1/4) p_{E,M}(c_M M) → 1/F(λ).
The convergence is locally uniform in λ.

## Proof

Use the exact Fock norm of §9 (label eg:thm:fock; equation eg:eq:norm),
already established in the manuscript. With r_E(z)=sin(z/2)/(z/2), it gives

    N_M(c) = (cM/π) ∫_{R²} exp[-cM(x²+y²)] |r_E(x+iy)|^(2M) dx dy.

Let Z=√12 U, m(z)=E exp(zZ)=sinh(√3 z)/(√3 z), with m(0)=1.
It is entire and even, and r_E(x+iy)=m((y-ix)/√12).
On a complex disk about zero, the analytic logarithm K=log m with K(0)=0 exists.
The convergent Taylor series gives

    m(z) = 1 + z²/2 + 3z⁴/40 + O(z⁶),
    K(z) = z²/2 - z⁴/20 + O(z⁶),
    κ_4(Z)=9/5-3=-6/5.

Use the anisotropic coordinates x=√6 M^(-1/2) w and y=√6 M^(-1/4) u.
The Jacobian is 6 M^(-3/4). Put q_M=(M^(-1/4)u-iM^(-1/2)w)/√2.
Consequently,

    N_M(c_M)/M^(1/4) = (6c_M/π) ∫_{R²} H_M(u,w) du dw,
    H_M = exp[-6c_M(√M u²+w²)] |m(q_M)|^(2M).

For each fixed u,w, q_M→0, M|q_M|⁶=O(M^(-1/2)). Therefore

    log H_M = -6c_M(√M u²+w²) + 2M Re K(q_M)
            → -w²-u⁴/40-6λu².

In particular the coefficient of w² is -1, not -1/2; the real and imaginary
directions contribute asymmetrically. The accompanying Lean candidate proves
the exact polynomial normal form of this exponent.

### Global domination (the essential nonlocal step)

For real h, let D(h)=h²/2-log m(h). For h≠0, D(h)>0:
coefficientwise comparison of the positive series
m(h)=Σ_{n≥0}3^n h^(2n)/(2n+1)! and exp(h²/2) follows from
(2n+1)!≥6^n n!, by induction using (2n+2)(2n+3)≥6(n+1).
The inequality is strict for n=2, proving strictness for h≠0.
Since D(h)/h⁴→1/20 at zero and D(h)/h²→1/2 at infinity
(the latter follows from 1≤m(h)≤exp(√3|h|)), continuity on the intervening
compact set yields a constant b>0 such that

    D(h) ≥ b min(h⁴,h²)   for all real h.

The triangle inequality for the expectation gives |m(h+ik)|≤m(h).
Set h=M^(-1/4)u/√2. Thus for all sufficiently large M, with c_M≥1/24,

    H_M ≤ exp[-w²/4+6|λ|u²-2Mb min(h⁴,h²)].

For |h|≤1 the last negative term equals -b u⁴/2.
For |h|>1 it equals -b√M u², so choose M sufficiently large that
b√M≥6|λ|+1. A single integrable dominating function is then

    exp(-w²/4) [ exp(6|λ|u²-bu⁴/2) + exp(-u²) ].

This proves domination on the entire plane, not merely on a truncated
critical region. The same dominating function works for |λ|≤L by replacing
|λ| with L, and the pointwise convergence is uniform in λ on that interval.
Dominated convergence now yields

    lim N_M(c_M)/M^(1/4)
        = (1/(2π)) ∫ exp(-w²-u⁴/40-6λu²) du dw = F(λ).

For λ=0 substitute t=u⁴/40 on the positive half-line and use the Gamma
integral, yielding the claimed constant. Since F(λ)>0, inversion gives
the vacuum probability asymptotic. No fixed-degree or Edgeworth expansion
has been interchanged with an uncontrolled integral or series.

## Lean milestones

1. Exact standardized moments, Taylor/log coefficients, factorial-series
   coefficient comparison, polynomial normal form and elementary tail bound:
   initial kernel candidate in CriticalWindowQuartic.lean (dedicated CI).
2. Establish the genuine complex Taylor remainder of m and its local analytic
   log, plus pointwise strict real MGF bound using the convergent series.
3. Prove the global deficit bound and |m(h+ik)|≤m(h) for the actual uniform law.
4. Instantiate the exact Fock norm and anisotropic change of variables;
   derive pointwise limit of the actual integrand and integrable majorant.
5. Apply dominated convergence to the product measure, evaluate the limiting
   Gaussian and Gamma integrals, invert to obtain the vacuum asymptotic.

The analytic steps 2–5 remain explicitly open in Lean. A successful initial
algebra CI is not a certificate of the full critical-window theorem.
