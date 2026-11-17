# Manuscript 16.6 certification scope — 17 November 2026

Authoritative supplied archive: Manoscritto_16_6_Reactive_Impedance_Holonomy_20261117(2).zip
SHA256: ed3877cbb2250598bda640ca05ddb69194f4b0675db165cc7dcc94fd71796cc3.

New source labels: thm:te-robin, cor:te-reactive, thm:holonomy-evan,
cor:hol-eulerian (§§14.4–14.5). Previous 16.5 obligations remain open;
this tranche does not duplicate #339–345. No manuscript/figure modifications.

| Source obligation | This tranche | Remaining |
|---|---|---|
| thm:te-robin | scalar impedance coefficient cancellation | actual curl system, boundary/domain, ODE uniqueness and L² fibre |
| cor:te-reactive | magnetic excess, actual half-line exponential integral, integrated imaginary flux coefficient | vector cross product and derivation from Maxwell solution |
| eq:hol-integral | actual scalar Lebesgue integral via Mathlib Gamma integral | abstract spectral theorem, trace summability, Tonelli and operator realisation |
| eq:hol-det | exact paired numerator cancellation | uniform convergence and Euler sine product applied to the circle spectrum |
| cor:hol-eulerian | exact scalar closed-form identities, strict bounds, cos half phase | connect spectral moments/product to closed forms, complex Eulerian profile, limiting assertions |

Bibliographic context as in source: Volakis (2019), Antenna Engineering
Handbook, §10.3 p.437; Keller (2000, 2011, 2012) for transverse field context;
the Gamma integral and hyperbolic duplication are classical. No novelty
assertion. The TE and holonomy models are kept independent.

Arb benchmarks use 3,600,000 working bits and individually assert at least
3,400,000 relative bits; exact dyadic endpoints strictly inside a unique
1,000,001-significant-decimal rounding cell (shared exact helper). The
nonzero scalar examples at unit TE parameters and two positive shifts are
explicitly chosen tests, not a complete operator or parameter-uniform proof.
Exact rationals/zero are separately documented. No old certificates removed.

Status: CANDIDATE pending exact-head Lean and Arb CI. No merge.
