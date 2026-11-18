# Manuscript 11 — rigorous million-digit Hausdorff minimiser

Source: the current 30-page author archive `Manuscript_11_Krapivsky_Luck_20261115(7).zip`, SHA-256 `4e1a28492c9e58bca106bdc97f82ba1d30f48a15b4f3c5175e5ea02e34fed1a3`; internal `11.pdf` SHA-256 `266cd62eddf952d4535a1964a7861b109f2a08d991e82d72dcd5f3c087a695b1`. References below follow that PDF.

## Proof of identification with the actual planar minimax root

Let P(theta) be the Eulerian curve, Z(t,h) the boundary of the convex body in Eq. (65), and d=P-Z. The system is

* d·d-h²=0,
* d·P'=0,
* d·Z'=0.

The implementation generates a numerical centre x=(theta,t,h) by adaptive Newton iteration. It uses only the midpoint as a candidate. With a fixed exact dyadic preconditioner B, an outward-rounded interval Jacobian on a coarse cube proves ||I-BJ||∞ < 1/2 throughout the cube. At 3,600,000 bits, ||BF(x)||∞ < 2^(-3480000)/2 is checked and the smaller cube fits in the coarse cube. B is nonsingular. The contraction mapping theorem proves a genuine exact zero in the small cube. Thus no conclusion relies on numerical Newton convergence alone.

At this zero, the displacement is perpendicular to the limaçon tangent, has norm h>0, and has positive scalar product with the outward normal. Since the body is strictly convex, the supporting half-plane proves Q(h)>=h. For the converse, on [1.98,2.22] choose the explicit path t(u)=t+u-theta. The squared distance along this path has derivative zero at theta. Its second derivative is strictly negative on the full central interval: the script verifies this with 240 interval panels at 160 bits covering the interval, uniformly for all points of the coarse root box. Consequently the squared distance along the chosen boundary path is at most h². Outside the interval, the radial comparison and concavity proved in Theorem 3.12 (Eqs. 62–64), with the checked endpoint inequalities, give distance <h. Reflection covers negative angles. These prove Q(h)<=h and hence Q(h)=h; uniqueness in Theorem 3.13 identifies h=h_*.

## Exact working precision and scope

The local 18 November 2026 execution at 3,600,000 working bits using python-flint 0.9.0 passed the strict exact-FLINT decimal rounding cells for all four of h_*, b_H, and both common-normal parameters. Minimum relative accuracy 3,479,994 bits. The script reuses `million_decimal_common.py`, which checks exact rational dyadic endpoints, a unique rounding to 1,000,001 significant decimal digits, and preserves outward ball/rounded digit records. GitHub CI must independently replay the exact head before repository certification is marked complete.

The separate derived job checks the two percentage gains, a_H, the total projected limaçon length via the complete elliptic integral, and the two normalized Krapivsky–Luck energy expressions (Eqs. 48b–c). The identity for the complementary energy uses the real-line Plancherel identity stated in the manuscript. The elliptic integral evaluates the projected limaçon (a_E,b_E), not the Hausdorff minimizer. Each is a candidate until its individual Arb rounding check passes.

**Remaining independent work:** Eulerian arclength and the normalized-arclength curvature diagnostic D_kappa (Eq. 50) at the requested million-digit precision. Their existing printed-precision certificates remain valid. No blanket claim of manuscript-wide million-digit coverage. This changes neither manuscript nor historical certificates.
