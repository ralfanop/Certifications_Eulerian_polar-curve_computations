# M11: independent midpoint panels for Eulerian arclength

This is a follow-up to #394 (20,000-bit success; experimental 100,000-bit
job timed out after 120 minutes) and the merged #389 (60,039 relative bits).
It addresses the same full Eulerian arclength, not a modified geometric
quantity. The latest author PDF (30 pages, page 26 editorial correction)
has SHA-256 `68522c012cd6b504696367a4f83ee66f72caaf8f6d4732881d5ac13d1a19326f`;
the correction does not alter any formula or equation number.

The existing analytic disk audit of #383 gives a zero-free speed square
F on |theta| <= 5 and |F| < 13. Let P be its even Taylor polynomial in
theta/5, with exact rational coefficients enclosed in Arb. The same
factorial coefficient ratio proof as #383 bounds |F-P| by eta on this
disk. Rouche's theorem and eta < 1/128 show that P has no zero there;
its positive-at-zero square root is analytic and bounded by 4.
For real theta in [0,pi], the previously proved F >= 4/pi^2 and
4/pi^2-eta > 1/4 imply |sqrt(F)-sqrt(P)| <= eta.

Divide [0,pi] into m equal panels, with midpoint c_j and half-width
h=pi/(2m). In x=(theta-c_j)/h, the analytic sqrt(P) has a Taylor
series whose coefficients have absolute bounds 4 rho_j^k, where
rho_j=h/(5-c_j)<1. In every panel use a separate affine polynomial
composition and FLINT series square root. The even coefficients give
the doubled panel integral 4h sum_{k even, k<N} s_k/(k+1).
The absolute enclosure radius is enlarged by
4h[4 rho_j^N/(1-rho_j)+eta]. The even order N is proposed by a float
only to select resources: the tail threshold is checked in outward
Arb arithmetic. No panel depends on another.

Each CI job emits its exact dyadic lower and upper bounds, index,
relative accuracy and resource measurements. Recombination checks all
indices occur once, sums exact rational endpoints, and checks the
final Arb enclosure's relative accuracy (not decimal display).
The CI target is 100,000 relative bits at 110,000 working bits;
it is explicitly an experimental scaling milestone, not the
1,000,001-significant-decimal certificate. No manuscript, figure,
historical certificate or existing workflow is changed.

Local pinned python-flint 0.9.0: eight independent panels and their
exact-endpoint recombination certified 5,031 relative bits; the
result overlaps the independent earlier 50k enclosure. The final
panel at 16 panels and target 20,000 achieved 20,031 bits in 7.78 s
(peak RSS 461,640 KiB). At 32 panels and target 50,000 it achieved
50,031 bits in 31.33 s (peak RSS 1,792,192 KiB).
