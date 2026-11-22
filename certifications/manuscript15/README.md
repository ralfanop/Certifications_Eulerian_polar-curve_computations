# Manuscript 15 — formal and numerical verification

Certification record: [Manuscript15_Certification.pdf](Manuscript15_Certification.pdf) ([Markdown](Manuscript15_Certification.md), [LaTeX](Manuscript15_Certification.tex)).

Snapshot: 22 November 2026. This record supersedes the manuscript's former Appendix B. The numbering below follows the revision of that date in which every displayed equation carries a single number, with no sub-numbers. Equations (1)–(190) keep their numbers; the former (190a) is (191); (191)–(237) became (192)–(238); the former (238a)–(238c) are (239)–(241); (239)–(272) became (242)–(275); the former (272a) and (272b) are (276) and (277); and (273) onwards became (278) onwards. The archived certificate files keep the earlier numbers: their equations (295) and (296) are the present (300) and (301). The library `M15Cert` and the 14-constant certificate, added the same day, also keep the earlier numbers in their source comments and files; the correspondence is given in their entries below. It identifies precisely the statements covered, rather than claiming certification of the entire article.

## Lean 4

- Lean 4.35.0-rc3; Mathlib pinned at `0272bbe1c093d038d7257ab15306abd58245f9ff`.
- 34 modules: build summary reports exit 0, zero errors, zero sorry; 508 axiom checks, only standard Lean axioms; 27 PrivateApex modules pass leanchecker.
- [Build summary](LOGS/SUMMARY.txt) · [Axiom checks](LOGS/AXIOMS.txt) · [Independent checker](LOGS/leanchecker.log) · [Source audit](LOGS/SOURCE_AUDIT.txt).
- [Source and reproducibility script](LEAN/) · [Complete logs](LOGS/) · [SHA-256 checksums](SHA256SUMS.txt).
- To reproduce, install the pinned toolchain via elan, enter `LEAN`, run `lake exe cache get` and `bash verify_all.sh`. Inspect the build, axiom and checker results. These archived results are verified again, independently, by GitHub Actions: [run 45045814495](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/45045814495) of the workflow `m15-certification.yml` rebuilt the 34 modules from source. It reproduced the 508 axiom lines identically, repeated the source audit and ran leanchecker on the 27 PrivateApex modules. It also reran both Arb certificates below with identical results.

The coefficients are defined by finite operations and evaluated exactly. The classical even-zeta evaluation is not required by these proofs. The following table reproduces the 132 named theorem correspondences from the former Appendix B.

| Statement | Lean theorems | Module(s) |
| --- | --- | --- |
| Definition 7.3 | `sOdd_is_slope`, `tEven_is_slope`, `plateau_level`, `virtual_apex_point`, `virtualApexAngle_eq` | [ApexDefinitions](LEAN/PrivateApex/ApexDefinitions.lean) |
| Theorem 7.4 | `alphaVirt_unique_min`, `alphaVirt_twelve`, `alphaVirt_three`, `alphaVirt_threshold`, `slopeQ_classification` | [ApexDefinitions](LEAN/PrivateApex/ApexDefinitions.lean), [GlobalApex](LEAN/PrivateApex/GlobalApex.lean) |
| Theorem 7.5 | `laplace_all_orders`, `odd_slope_all_orders`, `dC_unique`, `logC_table` | [LaplaceAllOrders](LEAN/PrivateApex/LaplaceAllOrders.lean), [SlopeAllOrders](LEAN/PrivateApex/SlopeAllOrders.lean), [LogSincSeries](LEAN/PrivateApex/LogSincSeries.lean) |
| Proposition 7.6 | `central_difference_add`, `slopeQ_even_eq`, `slopeQ_even_eq_integral` | [ConsecutiveSlopes](LEAN/PrivateApex/ConsecutiveSlopes.lean), [OddSlopeTail](LEAN/PrivateApex/OddSlopeTail.lean) |
| Corollary 7.7 | `even_of_odd_hasExp`, `even_slope_all_orders`, `eC_unique`, `eDirect_eq_eC` | [SlopeAllOrders](LEAN/PrivateApex/SlopeAllOrders.lean), [EvenDirect](LEAN/PrivateApex/EvenDirect.lean) |
| Table 2 | `cC_values`, `dC_values`, `eC_values` | [SlopeAllOrders](LEAN/PrivateApex/SlopeAllOrders.lean) |
| Eqs. (221), (223) | `slope_ratio_even_exact`, `slope_ratio_even_hasSum` | [ConsecutiveRatios](LEAN/PrivateApex/ConsecutiveRatios.lean) |
| Corollary 7.8 | `arctan_taylor`, `odd_angle_all_orders`, `even_angle_all_orders`, `odd_angle_eighth_order`, `even_angle_eighth_order` | [AngleAllOrders](LEAN/PrivateApex/AngleAllOrders.lean) |
| Table 3 | `angQ_dC_table`, `angQ_eC_table`, `dC_eq_dTab`, `eC_eq_eTab` | [AngleAllOrders](LEAN/PrivateApex/AngleAllOrders.lean) |
| Proposition 7.9 | `slope_ratio_odd_hasExp`, `slopeRatioOddQ_values`, `deficit_ratio_even_hasExp`, `deficit_ratio_odd_hasExp`, `deficitRatioEvenC_one`, `deficitRatioEvenC_two`, `deficitRatioOddC_one`, `deficitRatioOddC_two` | [ConsecutiveRatios](LEAN/PrivateApex/ConsecutiveRatios.lean), [DeficitRatioCoefficients](LEAN/PrivateApex/DeficitRatioCoefficients.lean) |
| Eqs. (242), (243) | `deficitRatioEvenC_three`, `deficitRatioEvenC_four`, `deficitRatioOddC_three`, `deficitRatioOddC_four` | [DeficitRatioCoefficients](LEAN/PrivateApex/DeficitRatioCoefficients.lean) |
| Theorem 7.10 | `odd_slope_remainder`, `even_slope_remainder`, `explicit_constants` | [QuantSlopes](LEAN/PrivateApex/QuantSlopes.lean) |
| Theorem 7.10 (continued) | `odd_slope_remainder_large`, `even_slope_remainder_large`, `odd_slope_remainder_power`, `even_slope_remainder_power` | [QuantSlopes](LEAN/PrivateApex/QuantSlopes.lean) |
| Eqs. (246)–(248) | `sin_taylor_sharp`, `log_hasExpQ`, `exp_neg_taylor`, `kap_pow_bound`, `laplace_explicit` | [QuantSinc](LEAN/PrivateApex/QuantSinc.lean), [LaplaceAllOrders](LEAN/PrivateApex/LaplaceAllOrders.lean), [QuantLaplace](LEAN/PrivateApex/QuantLaplace.lean) |
| Theorem 7.16 | `cardioid_sub_quarter`, `cardioid_eulerian`, `norm_cardioid_sub`, `eulerianB_exp`, `norm_eulerianB_exp`, `cardioid_eulerianB`, `rhoE_sq_mul`, `rhoE_sq_mul_neg_pi`, `rhoPole_sq_mul`, `one_sub_exp_eq_eulerianB`, `fixed_point`, `multiplier` | [CardioidIdentities](LEAN/PrivateApex/CardioidIdentities.lean) |
| Proposition 7.17 | `z0_sq`, `cardioid_special_point`, `special_point_unique` | [CardioidIdentities](LEAN/PrivateApex/CardioidIdentities.lean) |
| Theorem 7.19 | `charFun_unifLaw`, `charFun_unif01`, `charFun_unif01_eulerianB`, `triLaw_eq`, `cardioid_probabilistic`, `cardioid_expectation` | [CardioidProbability](LEAN/PrivateApex/CardioidProbability.lean) |
| Theorem 7.20 | `uniform_reconstructs`, `rigidity_local`, `rigidity_global`, `rigidity_iff` | [CardioidRigidity](LEAN/PrivateApex/CardioidRigidity.lean) |
| Proposition 7.22 | `hasDerivAt_cardioid`, `cardioid_zero`, `cardioid_pi`, `cardioid_re`, `cardioid_im`, `cusp_quotient_tendsto`, `period_two_factor`, `period_doubling`, `cusp_distance_rE`, `rE_pi` | [CardioidIdentities](LEAN/PrivateApex/CardioidIdentities.lean) |
| Eqs. (279)–(283) | `z1_eq_two_mul_z0`, `z1_eq_neg_inv_z0`, `z0_mul_z1`, `z1_sq`, `z0_add_z1`, `special_quadratic`, `quadratic_family_product`, `quadratic_family_involution`, `quadratic_family_factor`, `golden_quadratic`, `golden_other_root`, `S_smul_z0H`, `S_smul_z1H`, `modular_invariant_eq` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Proposition 7.24 | `cardioidFam_z0`, `cardioidFam_z1`, `cardioidFam_eulerian`, `cardioid_homothety` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Eqs. (288), (289) | `norm_cardioidFam_z0`, `norm_cardioidFam_z1`, `cardioidFam_pi`, `cardioidFam_pi_z0`, `cardioidFam_pi_z1`, `cardioidFam_half_pi_z0`, `cardioidFam_half_pi_z1`, `half_pi_ray` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Eqs. (290), (291) | `H4_eq`, `H4_cusp`, `H4_cardioid`, `hasDerivAt_H4`, `H4_dist`, `H4_dist_sq`, `H4_pullback` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |
| Eqs. (290), (291) (continued) | `H4_spherical_dilation_cusp`, `H4inf_eq`, `hasDerivAt_H4inf`, `H4_spherical_dilation_infinity`, `H4_not_modular` | [CardioidModular](LEAN/PrivateApex/CardioidModular.lean) |

### Library M15Cert

- Separate Lake project in [`LEAN/M15Cert`](LEAN/M15Cert): Lean 4.35.0-rc3; Mathlib tag `v4.35.0-rc3` (commit `c55e6e786f49471c72fbddbec5415808896aec1e`). It depends only on Mathlib and does not import or modify `PrivateApex` or `EulerianCert`.
- 7 modules, 98 theorems and lemmas, no `sorry`; 58 axiom checks, only standard Lean axioms; all 7 modules pass leanchecker. [Axiom checks](LEAN/M15Cert/axioms_output.txt) · [Independent checker](LEAN/M15Cert/leanchecker_output.txt) · [README and reproduction](LEAN/M15Cert/README.md).
- Verified again by GitHub Actions: [run 45051534998](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/45051534998) of the workflow `m15-m15cert.yml` rebuilt the 7 modules from source, reproduced the 58 axiom lines identically and ran leanchecker on the 7 modules.
- The sources and logs keep the earlier equation numbers: (262), (267) and (287)–(300) there are (265), (270) and (292)–(305) here.

| Statement | Lean theorems | Module(s) |
| --- | --- | --- |
| Proposition 7.25, Eqs. (292)–(296) | `rEc_differentiable`, `rEc_I_mul`, `catenoid_radius`, `catenoid_radius_eulerian`, `catenoid_circle_radius`, `deriv_catenoid_u`, `deriv_catenoid_v`, `catenoid_first_form`, `catenoid_metric`, `catNormal_unit_orthogonal`, `catenoid_second_form`, `catenoid_gaussian_curvature`, `catenoid_mean_curvature`, `catenoid_principal_curvatures` | [Kernel](LEAN/M15Cert/M15Cert/Kernel.lean), [Catenoid](LEAN/M15Cert/M15Cert/Catenoid.lean) |
| Theorem 7.26, Eqs. (297)–(300) | `catenoid_aspect`, `catenoid_aspect_eulerian`, `catenoid_aspect_eulerian_rEc`, `exists_unique_uStar`, `uStar_bounds`, `aspect_unique_max`, `lambdaCL_eq`, `lambdaCL_laplace_equation`, `laplace_equation_unique`, `bicone_inside`, `bicone_subset_catenoid`, `bicone_tangent`, `alphaCL_props`, `bicone_half_angle` | [CarliniLaplace](LEAN/M15Cert/M15Cert/CarliniLaplace.lean) |
| Proposition 7.27, Eqs. (302)–(305) | `ellL_eulerian`, `hasDerivAt_ellL`, `meridian_speed`, `ellL_eq_integral`, `sq_add_ellL_sq`, `ellis_eulerian`, `ellis_eulerian_rEc`, `ellis_equatorial_eq_catenoid`, `critical_length`, `critical_length_integral`, `critical_length_over_a` | [EllisMetric](LEAN/M15Cert/M15Cert/EllisMetric.lean) |
| Theorem 7.19, identification of the triangular density | `volume_overlap`, `law_sum_unif01`, `charFun_unif01`, `charFun_triLaw`, `cardioid_triLaw`, `map_unifC`, `law_one_add_sum_unifC`, `cardioid_probabilistic`, `eulerianB_eq_charFun_unif01` | [TriangularDensity](LEAN/M15Cert/M15Cert/TriangularDensity.lean) |
| Eq. (265), principal-root formulation | `sqrt_one_sub_four_cMand`, `cardioid_catalan_root`, `norm_one_sub_sqrt_cMand`, `fixed_point_eq_catalan`, `fixed_point_cMand` | [PrincipalRoot](LEAN/M15Cert/M15Cert/PrincipalRoot.lean) |
| Eq. (270), stability inequality | `charFun_sub_le_coupling`, `stability_coupling`, `cardioid_stability`, `cardioid_stability_real`, `prod_mem_couplings` | [Stability](LEAN/M15Cert/M15Cert/Stability.lean) |

## Numerical verification

- [Carlini–Laplace numerical certificate (ZIP)](ARB/M15_Eq295_FLINT_Arb_3600000bits.zip): 3,600,000 working bits; at least 3,599,870 bits relative accuracy for the four enclosed quantities. The printed 50-place degree value is certified under both truncation and rounding. [Run log](ARB/Carlini-Laplace/M15_eq295_run.txt) · [Reproduction script](ARB/Carlini-Laplace/certify_M15_eq295.py) · [README](ARB/Carlini-Laplace/M15_eq295_README.txt). This is an Arb enclosure, not a Lean proof of the catenoid theorem.
- [Minimum-apex Arb certificate (ZIP)](ARB/M15_virtual_apex_3600000bits.zip), containing the original exact binary endpoints, scripts, logs, and 1,000,001-place decimal files (radians and degrees; truncation and rounding). Operating precision 3,600,000 bits; relative accuracy 3,599,998 bits in radians and 3,599,996 bits in degrees. The original certificate refers to Theorem 7.3, now Theorem 7.4 after insertion of Definition 7.3. [Minimum-apex rational verification](verify_virtual_apex.py) independently checks the exact comparisons and the displayed decimal via rational alternating-series bounds.
- [Catenoid, transport and Gibbs-law certificate (ZIP)](ARB/M15_constants_FLINT_Arb_3600000bits_1000001digits.zip): 1,000,001 correctly rounded decimals of 14 constants, equations (298)–(301), (305), (370)–(374) and (416)–(419), computed at 3,600,000 working bits by two independent routes; every ball radius is at most 2^(−3599989). The certificate files call them (293)–(296), (300), (365)–(369) and (411)–(414). The fifty places displayed in the article coincide with the certified values. [Run log](ARB/Catenoid-Transport-Gibbs/run_stdout.txt) · [Reproduction script](ARB/Catenoid-Transport-Gibbs/m15_arb_certify.py) · [Certification log](ARB/Catenoid-Transport-Gibbs/certification_log.json) · [mpmath cross-check](ARB/Catenoid-Transport-Gibbs/m15_mpmath_crosscheck.py). Recomputed by [run 45051534998](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/45051534998), with identical decimal files.
- Additional [Eulerian angle checks](verify_eulerian_angles_n3_17_and_limit.py), [all-order jet checks](verify_all_order_jets.py), [sixth-moment checks](verify_cusp_sixth_moment.py).

## Limits of this record

Not included in this Lean correspondence: the numerical decimal evaluation of the minimum angle, the additional period-two disc derivation, and the conjecture on optimal remainder constants. A conjecture is not a verified theorem. Independent future work should be added only upon verification of its actual artifacts.

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
- [PR #504](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/pull/504) · [successful run 45051534998](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/45051534998): library M15Cert and the 14-constant Arb certificate.
