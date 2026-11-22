# Manuscript 15 — formal and numerical verification

Snapshot: 22 November 2026. This record supersedes the manuscript's former Appendix B; the numbering below follows the manuscript revision of that date. It identifies precisely the statements covered, rather than claiming certification of the entire article.

## Lean 4

- Lean 4.35.0-rc3; Mathlib pinned at `0272bbe1c093d038d7257ab15306abd58245f9ff`.
- 34 modules: build summary reports exit 0, zero errors, zero sorry; 508 axiom checks, only standard Lean axioms; 27 PrivateApex modules pass leanchecker.
- [Build summary](LOGS/SUMMARY.txt) · [Axiom checks](LOGS/AXIOMS.txt) · [Independent checker](LOGS/leanchecker.log) · [Source audit](LOGS/SOURCE_AUDIT.txt).
- [Source and reproducibility script](LEAN/) · [Complete logs](LOGS/) · [SHA-256 checksums](SHA256SUMS.txt).
- To reproduce, install the pinned toolchain via elan, enter `LEAN`, run `lake exe cache get` and `bash verify_all.sh`. Inspect the build, axiom and checker results. These are the archived results of the original verification, not a new GitHub CI run.

The coefficients are defined by finite operations and evaluated exactly. The classical even-zeta evaluation is not required by these proofs. The following table reproduces the 132 named theorem correspondences from the former Appendix B.

| Statement | Lean theorems | Module(s) |
| --- | --- | --- |
| Definition 7.3 | `sOdd_is_slope`, `tEven_is_slope`, `plateau_level`, `virtual_apex_point`, `virtualApexAngle_eq` | [ApexDefinitions](LEAN/PrivateApex/ApexDefinitions.lean) |
| Theorem 7.4 | `alphaVirt_unique_min`, `alphaVirt_twelve`, `alphaVirt_three`, `alphaVirt_threshold`, `slopeQ_classification` | [ApexDefinitions](LEAN/PrivateApex/ApexDefinitions.lean), [GlobalApex](LEAN/PrivateApex/GlobalApex.lean) |
| Theorem 7.5 | `laplace_all_orders`, `odd_slope_all_orders`, `dC_unique`, `logC_table` | [LaplaceAllOrders](LEAN/PrivateApex/LaplaceAllOrders.lean), [SlopeAllOrders](LEAN/PrivateApex/SlopeAllOrders.lean), [LogSincSeries](LEAN/PrivateApex/LogSincSeries.lean) |
| Proposition 7.6 | `central_difference_add`, `slopeQ_even_eq`, `slopeQ_even_eq_integral` | [ConsecutiveSlopes](LEAN/PrivateApex/ConsecutiveSlopes.lean), [OddSlopeTail](LEAN/PrivateApex/OddSlopeTail.lean) |
| Corollary 7.7 | `even_of_odd_hasExp`, `even_slope_all_orders`, `eC_unique`, `eDirect_eq_eC` | [SlopeAllOrders](LEAN/PrivateApex/SlopeAllOrders.lean), [EvenDirect](LEAN/PrivateApex/EvenDirect.lean) |
| Table 2 | `cC_values`, `dC_values`, `eC_values` | [SlopeAllOrders](LEAN/PrivateApex/SlopeAllOrders.lean) |
| Eqs. (220), (222) | `slope_ratio_even_exact`, `slope_ratio_even_hasSum` | [ConsecutiveRatios](LEAN/PrivateApex/ConsecutiveRatios.lean) |
| Corollary 7.8 | `arctan_taylor`, `odd_angle_all_orders`, `even_angle_all_orders`, `odd_angle_eighth_order`, `even_angle_eighth_order` | [AngleAllOrders](LEAN/PrivateApex/AngleAllOrders.lean) |
| Table 3 | `angQ_dC_table`, `angQ_eC_table`, `dC_eq_dTab`, `eC_eq_eTab` | [AngleAllOrders](LEAN/PrivateApex/AngleAllOrders.lean) |
| Proposition 7.9 | `slope_ratio_odd_hasExp`, `slopeRatioOddQ_values`, `deficit_ratio_even_hasExp`, `deficit_ratio_odd_hasExp`, `deficitRatioEvenC_one`, `deficitRatioEvenC_two`, `deficitRatioOddC_one`, `deficitRatioOddC_two` | [ConsecutiveRatios](LEAN/PrivateApex/ConsecutiveRatios.lean), [DeficitRatioCoefficients](LEAN/PrivateApex/DeficitRatioCoefficients.lean) |
| Eqs. (239), (240) | `deficitRatioEvenC_three`, `deficitRatioEvenC_four`, `deficitRatioOddC_three`, `deficitRatioOddC_four` | [DeficitRatioCoefficients](LEAN/PrivateApex/DeficitRatioCoefficients.lean) |
| Theorem 7.10 | `odd_slope_remainder`, `even_slope_remainder`, `explicit_constants` | [QuantSlopes](LEAN/PrivateApex/QuantSlopes.lean) |
| Theorem 7.10 (continued) | `odd_slope_remainder_large`, `even_slope_remainder_large`, `odd_slope_remainder_power`, `even_slope_remainder_power` | [QuantSlopes](LEAN/PrivateApex/QuantSlopes.lean) |
| Eqs. (243)–(245) | `sin_taylor_sharp`, `log_hasExpQ`, `exp_neg_taylor`, `kap_pow_bound`, `laplace_explicit` | [QuantSinc](LEAN/PrivateApex/QuantSinc.lean), [LaplaceAllOrders](LEAN/PrivateApex/LaplaceAllOrders.lean), [QuantLaplace](LEAN/PrivateApex/QuantLaplace.lean) |
| Theorem 7.16 | `cardioid_sub_quarter`, `cardioid_eulerian`, `norm_cardioid_sub`, `eulerianB_exp`, `norm_eulerianB_exp`, `cardioid_eulerianB`, `rhoE_sq_mul`, `rhoE_sq_mul_neg_pi`, `rhoPole_sq_mul`, `one_sub_exp_eq_eulerianB`, `fixed_point`, `multiplier` | [CardioidIdentities](LEAN/PrivateApex/CardioidIdentities.lean) |
| Proposition 7.17 | `z0_sq`, `cardioid_special_point`, `special_point_unique` | [CardioidIdentities](LEAN/PrivateApex/CardioidIdentities.lean) |
| Theorem 7.19 | `charFun_unifLaw`, `charFun_unif01`, `charFun_unif01_eulerianB`, `triLaw_eq`, `cardioid_probabilistic`, `cardioid_expectation` | [CardioidProbability](LEAN/PrivateApex/CardioidProbability.lean) |
| Theorem 7.20 | `uniform_reconstructs`, `rigidity_local`, `rigidity_global`, `rigidity_iff` | [CardioidRigidity](LEAN/PrivateApex/CardioidRigidity.lean) |
| Proposition 7.22 | `hasDerivAt_cardioid`, `cardioid_zero`, `cardioid_pi`, `cardioid_re`, `cardioid_im`, `cusp_quotient_tendsto`, `period_two_factor`, `period_doubling`, `cusp_distance_rE`, `rE_pi` | [CardioidIdentities](LEAN/PrivateApex/CardioidIdentities.lean) |
| Eqs. (274)–(278) | `z1_eq_two_mul_z0`, `z1_eq_neg_inv_z0`, `z0_mul_z1`, `z1_sq`, `z0_add_z1`, `special_quadratic`, `quadratic_family_product`, `quadratic_family_involution`, `quadratic_family_factor`, `golden_quadratic`, `golden_other_root`, `S_smul_z0H`, `S_smul_z1H`, `modular_invariant_eq` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Proposition 7.24 | `cardioidFam_z0`, `cardioidFam_z1`, `cardioidFam_eulerian`, `cardioid_homothety` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Eqs. (283), (284) | `norm_cardioidFam_z0`, `norm_cardioidFam_z1`, `cardioidFam_pi`, `cardioidFam_pi_z0`, `cardioidFam_pi_z1`, `cardioidFam_half_pi_z0`, `cardioidFam_half_pi_z1`, `half_pi_ray` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Eqs. (285), (286) | `H4_eq`, `H4_cusp`, `H4_cardioid`, `hasDerivAt_H4`, `H4_dist`, `H4_dist_sq`, `H4_pullback` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Eqs. (285), (286) (continued) | `H4_spherical_dilation_cusp`, `H4inf_eq`, `hasDerivAt_H4inf`, `H4_spherical_dilation_infinity`, `H4_not_modular` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |

## Numerical verification

- [Carlini–Laplace numerical certificate (ZIP)](ARB/M15_Eq295_FLINT_Arb_3600000bits.zip): 3,600,000 working bits; at least 3,599,870 bits relative accuracy for the four enclosed quantities. The printed 50-place degree value is certified under both truncation and rounding. [Run log](ARB/Carlini-Laplace/M15_eq295_run.txt) · [Reproduction script](ARB/Carlini-Laplace/certify_M15_eq295.py) · [README](ARB/Carlini-Laplace/M15_eq295_README.txt). This is an Arb enclosure, not a Lean proof of the catenoid theorem.
- [Minimum-apex Arb certificate (ZIP)](ARB/M15_virtual_apex_3600000bits.zip), containing the original exact binary endpoints, scripts, logs, and 1,000,001-place decimal files (radians and degrees; truncation and rounding). Operating precision 3,600,000 bits; relative accuracy 3,599,998 bits in radians and 3,599,996 bits in degrees. The original certificate refers to Theorem 7.3, now Theorem 7.4 after insertion of Definition 7.3. [Minimum-apex rational verification](verify_virtual_apex.py) independently checks the exact comparisons and the displayed decimal via rational alternating-series bounds.
- Additional [Eulerian angle checks](verify_eulerian_angles_n3_17_and_limit.py), [all-order jet checks](verify_all_order_jets.py), [sixth-moment checks](verify_cusp_sixth_moment.py).

## Limits of this record

Not included in this Lean correspondence: identification of the triangular density, the principal-root formulation, the stability inequality, the numerical decimal evaluation of the minimum angle, the additional period-two disc derivation, the catenoidal reconstruction section, and the conjecture on optimal remainder constants. A conjecture is not a verified theorem. Independent future work should be added only upon verification of its actual artifacts.

## Other repository evidence

The following workflow runs succeeded; each has its own scope. This list is not a claim that every extension in Manuscript 15 is certified.

- [PR #325](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/325) · [successful run 43724374973](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43724374973): Lean and Arb checks.
- [PR #338](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/338) · [successful run 43921559615](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43921559615): geometry and magnetic checks.
- [PR #378](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/378) · [successful run 44296095160](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44296095160): Lean and Arb checks.
- [PR #435](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/435) · [successful run 44494713791](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44494713791): terminal Taylor jets (partial scope).
- [PR #437](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/437) · [successful run 44495582023](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44495582023): Möbius spectral sine-integral.
- [PR #457](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/457) · [successful run 44518261905](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44518261905): exponential atom masses, W-infinity.
- [PR #464](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/464) · [successful run 44519321578](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44519321578): Gaussian integrals.
- [PR #470](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/470) · [successful run 44743294532](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44743294532): exact local W1/W2 costs, not global sums.
- [PR #491](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/491) · [successful run 44918198103](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/44918198103): inverse recurrence, not closed Lagrange–Bürmann.
- [PR #497](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/497) · [run 45034350299](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/45034350299): failed; not counted as certified.
