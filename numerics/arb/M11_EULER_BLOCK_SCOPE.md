# Manuscript 11: finite-width rigorous arclength recurrence

Source: current 30-page `11.pdf` SHA-256 `266cd62eddf952d4535a1964a7861b109f2a08d991e82d72dcd5f3c087a695b1`. This is a scaling experiment for the full Eulerian length, not a million-digit certificate. It uses the independently audited analytic disk and uniform speed-square truncation from PR #383.

Write P(u) for the truncated speed-square polynomial, q=pi^2/25 and S(u)=sqrt(P(u)). P(0)=S(0)=1 and 2PS'=P'S. With a_j=P_j q^j and t_n=S_n q^n, comparison of coefficients gives

    2n t_n = sum_{j=1}^{min(n,K)} (3j-2n) a_j t_{n-j},

where K=deg(P). Thus the next block requires only the last K scaled coefficients, not the complete length-N series. Two convolutions provide contributions from known history; a short inner recurrence supplies contributions from earlier terms in the same block. Kernel partitioning further limits temporary product sizes. Specifically, for a kernel interval [j0,j1), history indices l=max(0,m-j1+1) through r-1=min(m,m+B-j0)-1 suffice for outputs m,...,m+B-1, where m is current history length and B is block size. Each product coefficient is selected at m+k-j0-l for output k. The other convolution weights a_j by j. Ordinary Arb interval arithmetic encloses all operations, including those carried out at adaptively lowered precision. The final threshold is measured from the resulting ball, not inferred from working precision.

Integrate by summing 2*pi*t_n/(2n+1); the rigorous tail remains 8*pi*q^N/(1-q)+2*pi*eta, with eta=2^(-target-40). The omitted speed-square coefficients have geometric ratio <1/2 from k>=5. The code checks the hypotheses of the analytic disk bound, the final interval and the required relative precision, then emits exact dyadic endpoints. Recycling the last K values reduces storage from O(N) to O(K), with optional chunking of convolutions. It does not establish feasibility at 3,400,000 relative bits: retained history and kernel remain substantial at that scale, and the total work still increases sharply.

Local pilots: at 4,096 working bits the adaptive chunked method passed 3,000 relative bits; at 28,000 working bits the unchunked method achieved 20,334 relative bits. The CI stages independently exercise chunked 20,000 and experimental 60,000 relative-bit thresholds. The existing remotely verified best length result is 50,808 relative bits (PR #383); it is not superseded until a stronger successful run exists. No manuscript or historical certificate is changed.
