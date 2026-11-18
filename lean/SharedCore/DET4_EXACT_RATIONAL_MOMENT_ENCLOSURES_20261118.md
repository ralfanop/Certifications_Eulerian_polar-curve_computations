# Shared det4: exact rational fourth-moment enclosures and certified truncation route

Date: 2026-11-18. Supplement to Draft #376 and the diagonal test model #373. This is an **analytic proof**, not a Lean/Arb certificate and not an identification with a physical operator.

Let m_n=(n+1)(n+2), lambda_n=1/(n+2). For integer N>=2 define the **exact rational**

    A_N = sum_{k=2}^N (k-1)/k^3 = sum_{k=2}^N (1/k^2 - 1/k^3).

Then A=Tr(T^4)=zeta(2)-zeta(3) satisfies the rigorous rational enclosure

    A_N < A < A_N + 1/N.

Proof: A-A_N=sum_{k=N+1}^infinity (k-1)/k^3 is positive and strictly smaller than sum_{k=N+1}^infinity 1/k^2. Since x -> x^(-2) is strictly decreasing, sum_{k=N+1}^infinity 1/k^2 < integral_N^infinity x^(-2) dx = 1/N. No floating-point assumptions are used. For every integer q>=4, the same argument gives the exact rational interval for M(q)=sum_{k=2}^infinity (k-1)k^(1-q):

    M_N(q) := sum_{k=2}^N (k-1)/k^(q-1),
    M_N(q) < M(q) < M_N(q) + N^(3-q)/(q-3).

Indeed (k-1)k^(1-q)<k^(2-q) and the decreasing integral bound is integral_N^infinity x^(2-q) dx. For q=4 this reproduces 1/N.

For the logarithmic fourth Taylor coefficient c4=-A/4, this yields the **exact rational** interval

    -(A_N+1/N)/4 < c4 < -A_N/4.

The fourth derivative D4''''(0)=-6A is correspondingly enclosed between -6(A_N+1/N) and -6A_N. These inequalities provide an independent exact regression test for future Arb output and can be formalized using finite rational sums and integral comparison. They do not require a zeta-function implementation in Lean.

**Important precision limitation.** The O(1/N) enclosure alone is computationally unsuitable for 1,000,001 significant decimal digits: its width is far too large for feasible N. It must **not** be represented as meeting the user's 3,600,000-bit / 3,400,000-bit / rounding-cell standard. For high precision, use a rigorously bounded accelerated zeta evaluation or Euler–Maclaurin scheme and verify individual Arb balls with exact rounding-cell endpoints. Rational A_N itself is exact and must not be assigned a fictitious relative accuracy.

The statements here are classical p-series integral-comparison bounds, not new original theorems. They are confined to the diagonal fixture, do not resolve the actual operator's Schatten membership, and do not modify manuscript sources or figures. No merge.
