# Manuscript 11 — scaling the two remaining validated quadratures

Source: the 30-page author archive SHA-256 `4e1a28492c9e58bca106bdc97f82ba1d30f48a15b4f3c5175e5ea02e34fed1a3`; `11.pdf` SHA-256 `266cd62eddf952d4535a1964a7861b109f2a08d991e82d72dcd5f3c087a695b1`. This is an independent scaling pilot for Eq. (50) and the Eulerian full length immediately following it. Both exact-head jobs of PR #381 (Hausdorff minimizer and derived quantities including projected limaçon length) already succeeded. **These new pilot thresholds are not the 1,000,001-digit target.**

## Eulerian length

For r(t)=sinc(t/2), the even entire function F=r²+r'² satisfies

    t^4 F(t) = (5/2)t² - (3/2)t² cos(t) - 2t sin(t) + 2(1-cos(t)).

Its Taylor coefficient of t^(2k) equals (-1)^k [(3/2)(2k+4)(2k+3)+2(2k+4)-2]/(2k+4)!. A finite exact dyadic rectangle cover of the disk |t|<=5 uses complex Arb 0F1 enclosures to exclude zeros of both factors r+i r' and r-i r'. Thus the positive-at-zero analytic square root exists on the disk, is even, and by absolute Taylor majorants has modulus <4. In the variable u=t²/25, its Taylor coefficients are bounded by 4 by Cauchy's estimate. The integral 2∫_0^π sqrt(F(t)) dt follows by series integration, with a rigorous geometric tail <=8π q^N/(1-q), q=π²/25. No numerical agreement is used as a proof. The output records exact rational dyadic endpoints and measured relative bits.

## Curvature discrepancy after independent normalized arclength

Use the same exact reduction as the existing validated Eq. (50) certificate. For each curve define H(x)=π sqrt(r²+r'²) at t=πx, ell=∫_0^1 H(x)dx, and K(x)=(r²+2r'²-r r'')/(r²+r'²)^(3/2). Both real curvatures are positive on the smooth arc by the manuscript's inequalities. On the exact strip rectangle [-3/8,11/8]+i[-3/8,3/8], a dyadic tile audit in Acb proves for both curves Re(r²+r'²)>0, Re H>6/5, |H|<4, |K|<35. Hence H and K are analytic there. Each chart length ell<3 is certified by Taylor integration with explicit Cauchy tails.

The normalized arclength primitive A/ell is injective on the convex rectangle because Re H>6/5. On every disk of radius 3/8 about a real x∈[0,1], the difference from its centre value has modulus >(6/5)(3/8)/ell>3/20 on the circle. By Rouché and the nonzero derivative, the inverse x(u) is holomorphic on the disk of radius 3/20 centered at the corresponding real u. Thus the squared curvature difference is analytic there with modulus <4900. This bounds its integrated Taylor remainder geometrically. Real inverse root balls are still certified by the residual and the existing real speed lower bound H>=2, not by Newton convergence. Local derivative jets use the existing certified radial Taylor tails and formal series reversion. The new algorithm avoids wide high-order inverse Taylor evaluations, and outputs exact dyadic endpoints for each quantity.

The local first pilots give 3065 relative bits for Eulerian length and 536 relative bits for D_kappa. The original independent direct Arb quadrature gave 9988 relative bits for Eulerian length; the prior Taylor implementation gave 978 relative bits for D_kappa at order 256, 2048 working bits. Larger tests are genuine scaling experiments. The full million-digit threshold requires substantially greater computational resources or additional algorithmic compression, especially the high-degree power series/reversion. No claim of blanket certification is made. No historical certificates or manuscripts changed.
