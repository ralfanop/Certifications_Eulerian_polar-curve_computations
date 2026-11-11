# Manuscript 15 — exact Eulerian n=3 apex geometry, Figure 1

The source Figure 1 shows the 7000 Eulerian profiles n=3,...,7002
in an isometric (x_{n,k}, p_{n,k}) coordinate system.

The n=3 Eulerian distribution is exactly
`E(3,.)=[1,4,1]`, hence probabilities `(1/6,2/3,1/6)`
at abscissae `(1/4,1/2,3/4)`.

This Lean candidate reuses the **actual** Manuscript 11 Eulerian
number recursion in `EulerianCert.Bracket`, checks the n=3 row in
the Lean kernel, and proves:
- left side slope +2, right side slope -2;
- two inward side vectors with common squared norm 5 and dot
  product 3, yielding a cosine ratio of 3/5;
- `tan(α₃/2)=1/2` for `α₃=2 atan(1/2)`.

The numerical value `α₃≈53.1301023542°` is separately certified
at 10000-bit Arb precision in PR #179, exact-head CI #43080355596.

**Scope:** This PR does not modify the Figure 1 vector PDF and does
not claim that an SVG/PGF arc's endpoints are certified by Lean.
Also, the complete geometric identification of the angle as the
principal arccos(3/5) is left for an additional theorem; this file
certifies its exact slopes and half-angle tangent.

Candidate until exact-head kernel CI succeeds, then the source
declarations (and no more) may be described as Lean-certified.
No merge.
