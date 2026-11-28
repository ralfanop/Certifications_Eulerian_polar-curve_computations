# M14: next saturation and quartic results

This PR extends the previously audited actual Langevin inverse and finite-spin Gibbs law. It proposes 17 kernel checks: exact positive threshold correction, algebraic reference and exact decomposition; exact scaled variance factor and limit e^t I(t) -> 1, e^(t/2) sqrt(I(t)) -> 1 for fixed n>0; completed square, perfect-square locus and reduction for Proposition 4.5. No new audit result is asserted until CI completes. The full large-spin remainder bound and the limit e^(t/2) d_F(t,+infty) -> 2 are separate analytic obligations; pointwise speed asymptotics alone do not certify the latter. No physical field generation or wormhole claim is made.

Stacked candidate layer: sharp actual intrinsic Fisher saturation distance (two declarations), Gerono zero locus, minimum equality locus and algebraic self-dual energy (three declarations). The elliptic density integral and uniform-in-spin limit are not claimed. Await exact-head audit.
