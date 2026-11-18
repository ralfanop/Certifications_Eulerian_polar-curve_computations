# M11: validated scalar ODE acceleration for the curvature discrepancy

Source: author archive SHA256 `4e1a28492c9e58bca106bdc97f82ba1d30f48a15b4f3c5175e5ea02e34fed1a3`, internal 30-page `11.pdf` SHA256 `266cd62eddf952d4535a1964a7861b109f2a08d991e82d72dcd5f3c087a695b1`. This is a new scaling pilot for D_kappa in Eq. (50), not a million-digit claim. The previous PR #383 is merged and its exact-head runs certified 50,808 relative bits for Eulerian length and 2,175 for D_kappa.

## Mathematical reduction and rigorous local series

Write ell_i for the two half-lengths and v_i(theta)=sqrt(r_i^2+(r_i')^2). In normalized half-arclength u the inverse satisfies d theta_i/du=ell_i/v_i(theta_i). For local variable z=(u-u0)/s the ODE is y'=F(y), F(y)=s ell_i/v_i(y). On every real interior panel the initial point y(0) is enclosed by the previously proved real residual bound with H_i>=2, using the exact arclength primitives below. The curvature is the exact rational expression (r²+2r'²-r r'')/v³. For the Eulerian curve, r=2 sin(theta/2)/theta and r''=-2r'/theta-r/4; at each panel centre theta>0. No assumption of numerical Newton convergence is used.

If the current polynomial y contains the exact first m coefficients, the true solution differs by delta=O(z^m). The linearized correction has equation delta'=F'(y)delta+F(y)-y', delta(0)=0, where F'=-s ell_i r'(r+r'')/v³. The discarded nonlinear remainder is O(z^(2m)), hence the correction obtained with an integrating factor determines coefficients through degree 2m-1. Because y' has degree at most m-2 and the residual starts at degree m-1, only the shifted residual is needed. Put k=d-m, d=min(2m,order), G=exp(integral(F'(y))) truncated to k terms, and Rt_j=F(y)_(m-1+j). Then delta=z^m G W with W_j=(G^(-1) Rt)_j/(m+j). This proves by induction that the Arb ball arithmetic encloses all local Taylor coefficients, avoiding generic series reversion and composition.

The previous exact complex-strip certificate proves holomorphic inverses on every disc of radius R=3/20 in normalized arclength, with |K_E-K_L|²<4900. Thus the integrated tail in a real panel of halfwidth h is bounded by 2h*4900*(h/R)^p / ((p+1)*(1-h/R)), independently of the variable scale s. The weighted polynomial integral uses 2h*f_k*(h/s)^k/(k+1) for even coefficients k. Adaptive working precision is a resource allocation heuristic only; every Arb operation remains outward rounded, and final relative-accuracy thresholds are mandatory.

## Primitive evaluation

For the Eulerian curve, reuse the single zero-free-disc Cauchy polynomial of PR #383. With q=theta²/25 and the bounded polynomial speed-square approximation error eta, the exact primitive is enclosed by theta*sum S_k q^k/(2k+1) plus/minus [4 theta q^N/(1-q)+theta eta]. No piecewise arclength tables are stored. For the projected limaçon we use the exact incomplete elliptic integral 2(a_E+b_E) E(theta/2, k²), k²=4a_E b_E/(a_E+b_E)², and its complete value at theta=pi. Both are rigorously evaluated using Acb. The residual bound proves the initial point for each ODE jet, regardless of Newton's candidate accuracy.

## Scaling results and limitation

Local 4,096-working-bit ODE pilot (order 1024, 16 panels) certified 2,310 relative bits in 79.3 seconds, compared with 2,175 relative bits in 229.4 seconds in the previous exact-head CI. The streamlined global primitive + adaptive ODE implementation passes the local order-128 pilot with 536 relative bits. New CI targets 3,000 verified relative bits for order 1024, 32 panels, 4,096 working bits. Exact dyadic endpoints are emitted. The required 3,400,000 relative bits and strict 1,000,001 significant-digit cell remain open, as does the million-digit Eulerian length. No manuscript, figures or previous certificates modified.
