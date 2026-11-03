# Manuscript 14.9 — Section 11: prior-art and certification audit

Date: 3 November 2026. Manuscript version: 14.9 (35 pages).
Scope: only the new Eulerian/Parry dynamics Section 11. No claims for the
pre-existing operator results in Sections 1–10; V007 and V097 untouched.

## Prior-art outcome (conservative)

| Manuscript claim | Relevant known theory | Novelty classification |
| --- | --- | --- |
| The family F_n(t)=t^(n−1)(t−1)−1, unique root beta_n in (1,2), finite greedy digit word 1 0^(n−2) 1 | Parry 1960; Hare–Hichri arXiv:2603.19554 (Mar 2026), §3.1 expressly treats x^d−x^(d−1)−1; Cornean–Herbst–Sørensen arXiv:2610.27844 (20 Oct 2026), §§1.3, E.2 expressly studies same polynomials | PRE-EXISTING, do not claim novelty for family/finite expansion |
| Parry invariant density h_beta=Z^-1 sum beta^-n 1_[0,T_beta^n(1)) | Gelfond–Parry 1960; modern treatments of beta-transfer operators | CLASSICAL, not new |
| Fourier integral of interval 1_[0,t_n) expressed by sinc r_E | Elementary translated interval identity | EXACT but ROUTINE consequence of the classical density |
| Dyadic cos product r_E(z)=prod_{k>=1}cos(z/2^(k+1)) | Standard infinite product for sin/characteristic function of binary uniform measure | CLASSICAL |
| Eulerian parameter x_E=sqrt(2)sinh(1/sqrt(2)) and rational-certified bracket beta_32<x_E<beta_31 | Search of the cited works and the two 2026 preprints did not locate this special-value comparison | POSSIBLY NEW numerical/symbolic specialisation, NOT established comprehensive priority |
| Initial greedy prefix 1 0^30 1 and strict orbit defect near the beta_31 threshold | Direct application of known beta-expansion transition and rational bounds | A new evaluated example, not a new general theory |
| Non-eventual-periodicity of the greedy expansion of x_E | Elementary: eventually periodic greedy expansion implies algebraic beta; Lindemann yields transcendental x_E | STANDARD inference applied to this parameter |
| 31=2^5-1 (third Mersenne prime) | Elementary number theory | NUMERICAL COINCIDENCE; no proved Mersenne-dependent mechanism |

## Two recent sources crucial to priority

1. K. G. Hare and H. Hichri, *The Parry Order of Perron Numbers*,
   arXiv:2603.19554v1, 20 March 2026,
   https://arxiv.org/html/2603.19554v1 .
   Section 3.1 explicitly states that all roots theta_d of
   x^d−x^(d−1)−1 are simple Parry and that
   d_{theta_d}(1)=1 0^(d−2) 1.
2. H. D. Cornean, I. W. Herbst, K. S. Sørensen,
   *Beta-expansions induced by general Parry polynomials and sharp
   iteration asymptotics of their transfer operators*,
   arXiv:2610.27844, posted 20 October 2026,
   https://arxiv.org/abs/2610.27844 .
   Sections 1.3 and Appendix E.2 explicitly consider
   p_n(z)=z^n−z^(n−1)−1 and its zeros.
   Their spectral assertions have additional hypotheses: do NOT
   transfer spectral conclusions to beta_31 without checking them.

Other fundamental primary references: W. Parry (1960),
doi:10.1007/BF02020954; K. Schmidt (1980),
doi:10.1112/blms/12.4.269; K. G. Hare and D. Tweedle (2008),
doi:10.1016/j.jnt.2008.02.010; B. Melo Maia (2017),
doi:10.1080/14689367.2017.1288701;
B. Quackenbush, T. Samuel, M. West (2020),
doi:10.3390/math8060903; M. J. Bertin et al. (1992),
doi:10.1007/978-3-0348-8632-1 .

Verger-Gaugry (arXiv:2401.05843) uses theta_31^(-1) as a *claimed*
lower Salem bound; its status must not be equated with a generally
accepted solution of Lehmer's problem. The comparison with theta_31 is
unconditional as an algebraic/symbolic statement and does not depend
on accepting the claimed universal Salem lower bound.

## Independent numerical facts

Define x_E=sqrt(2)sinh(1/sqrt(2)) and
F_n(t)=t^(n−1)(t−1)−1.
- beta_31 = 1.085449604556998884752545618734...
- x_E     = 1.085441641272607001869623081077...
- beta_32 = 1.083421560363417805803669241339...
- delta_E = 1−x_E^30(x_E−1)
          = 0.0003132406153157297645163390525...

The exact rational script uses the positive Taylor series
x_E=sum_{k>=0}1/(2^k(2k+1)!), a rigorous geometric tail enclosure,
exact rational sign tests F_32(1.0854)>0.01 and
F_31(1.085445)<−0.0001, and 20-decimal root isolations.
The Arb job uses python-flint==0.9.0, 256-bit real balls; the Lean file
proves rational comparisons and conditional transport of inequalities.

## Strict verification boundary

- Arb proof-of-sign and numeric enclosure: independently executable.
- Lean polynomial-sign lemmas and strict interval transport: five theorems
  **SUCCESS** on CI #41725449416 (pinned Lean 4.35.0-rc3, Mathlib;
  #print axioms includes only propext, Classical.choice, Quot.sound).
  The sixth exact two-digit identity is also Lean-certified: CI #41726344450
  SUCCESS (all six declarations audited, only the three standard axioms).
  There remains no Lean certificate for the analytic identity
  x_E=sqrt(2)sinh(1/sqrt(2)) or the full Perron–Frobenius invariant-density theorem.
- Transcendence uses Lindemann's theorem in the manuscript; not Lean-certified
  by this Section 11 module.
- The Mersenne-index conjecture is not proved.
- No merge to V007, V097, or main.

## Recommended scholarly framing

Title the new section as in 14.9. Cite Hare–Hichri (Mar 2026) and
Cornean–Herbst–Sørensen (Oct 2026) before any priority wording.
Label the two old general constructions classical; present the
special Eulerian bracketing, digit boundary and certified defect as a
sharp, reproducible specialisation. The next substantive new result
would require a theorem about parameter-dependence of invariant
densities or a genuinely new spectral relation; no such theorem has
yet been established.
