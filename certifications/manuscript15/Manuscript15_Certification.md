# Manuscript 15: Lean 4 and Arb certification record

*Cycloidal reconstruction and probabilistic rigidity of Eulerian Fourier profiles*. Roberto Alfano, 22 November 2026. This record is also available as [Manuscript15_Certification.pdf](Manuscript15_Certification.pdf) and [Manuscript15_Certification.tex](Manuscript15_Certification.tex); the index of the archive is [README.md](README.md).

## 1. Scope.

This record states, for manuscript 15, which results are kernel-checked in Lean 4 [3], which values are certified in Arb ball arithmetic [1] and how both are rebuilt and checked again. It replaces the former Appendix B of the article (correspondence between statements and Lean theorems). Equation, section and result numbers are those of the revision of 22 November 2026 that cites this record. All files named below are in the directory [`certifications/manuscript15`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/tree/main/certifications/manuscript15) of the repository https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations.

## 2. Lean 4: the libraries `PrivateApex` and `EulerianCert`.

The formalisation comprises 34 modules, in the directory [`LEAN`](LEAN): 27 modules of the library `PrivateApex` and 7 modules of the library `EulerianCert`. The 7 modules of `EulerianCert` are byte-identical to those of the same name in [`lean/EulerianCert`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/tree/main/lean/EulerianCert). They are compiled with the Lean 4 toolchain `v4.35.0-rc3` and Mathlib [2] commit `0272bbe1c093d038d7257ab15306abd58245f9ff`. No module contains `sorry`, `admit`, `native_decide` or an `axiom` declaration. The command `#print axioms` was run on each of the 508 theorems of `PrivateApex`:

- 505 theorems depend only on `propext`, `Classical.choice` and `Quot.sound`;
- 2 depend only on `propext` and `Quot.sound`;
- 1 depends only on `propext`.

The independent checker `leanchecker` accepts all 27 modules of `PrivateApex`. The archived logs are [`LOGS/SUMMARY.txt`](LOGS/SUMMARY.txt) (build), [`LOGS/AXIOMS.txt`](LOGS/AXIOMS.txt) (axioms), [`LOGS/SOURCE_AUDIT.txt`](LOGS/SOURCE_AUDIT.txt) (source audit) and [`LOGS/leanchecker.log`](LOGS/leanchecker.log), with the checksums in [`SHA256SUMS.txt`](SHA256SUMS.txt).

The archive is verified again, independently, by the workflow [`m15-certification.yml`](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/blob/main/.github/workflows/m15-certification.yml), in [run 45045814495](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/45045814495) (commit `a774edaa`), which:

- checks the checksums;
- rebuilds the 34 modules from source;
- prints the axioms of the 508 theorems again and requires the output to equal `LOGS/AXIOMS.txt` line by line, with only the three standard axioms;
- repeats the source audit;
- runs `leanchecker` on the 27 modules of `PrivateApex`.

To reproduce locally, install the toolchain of `LEAN/lean-toolchain` with elan, enter `LEAN`, and run `lake exe cache get` and then `bash verify_all.sh`.

## 3. Statements and Lean theorems.

Each statement of the article listed below is the conclusion of the named Lean theorems (132 in all), in the modules shown. No result is assumed as an axiom: the only axioms used are the standard ones listed in Section 2.

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

## 4. Arb certificates at 3600000 bits.

Both certificates use FLINT/Arb [1] through python-flint 0.9.0. The same run 45045814495 recomputed both of them and found the archived results again byte for byte: the enclosures, the exact binary endpoints and the decimal files.

- **Carlini–Laplace angle, equations (295)–(296).** The unique positive root u\* of u tanh u = 1 is enclosed between exact dyadic endpoints with interval signs of opposite strict sign. Its uniqueness follows from tanh u + u sech²u > 0 for u > 0. The enclosure is propagated to λ = (u\*² − 1)^(1/2), α = 2 arctan(1/λ) and to degrees, and checked against equivalent formulas in sinh u\* by overlap. The working precision is 3600000 bits and the relative accuracy is at least 3599870 bits. The printed 50-place value 112.93167025490469621261195929014436025897847010921393° is certified under both truncation and rounding. This is a numerical enclosure, not a Lean proof of the catenoid theorem. Files: [certificate (ZIP)](ARB/M15_Eq295_FLINT_Arb_3600000bits.zip), [script](ARB/Carlini-Laplace/certify_M15_eq295.py), [run log](ARB/Carlini-Laplace/M15_eq295_run.txt), [README](ARB/Carlini-Laplace/M15_eq295_README.txt).

- **Minimum apex angle, Theorem 7.4.** The angle 2 arctan(3628800/9473633) is computed at 3600000 bits and checked by overlap against the arccosine formula. Its relative accuracy is 3599998 bits in radians and 3599996 bits in degrees. Exact rational comparisons of the endpoints certify 1000001 decimal places, in radians and in degrees, under both truncation and rounding. The archive contains the exact binary endpoints, the four decimal files, the scripts and the logs. Files: [certificate (ZIP)](ARB/M15_virtual_apex_3600000bits.zip). The original certificate refers to Theorem 7.3, which is Theorem 7.4 after the insertion of Definition 7.3.

## 5. Exact rational and symbolic checks.

Four further scripts run in the same workflow:

- [`verify_virtual_apex.py`](verify_virtual_apex.py) repeats the exact comparisons of Theorem 7.4 and checks the displayed 50-place decimal by rational alternating-series bounds.
- [`verify_all_order_jets.py`](verify_all_order_jets.py) checks the all-order jets.
- [`verify_cusp_sixth_moment.py`](verify_cusp_sixth_moment.py) checks the sixth-order cusp coefficients.
- [`verify_eulerian_angles_n3_17_and_limit.py`](verify_eulerian_angles_n3_17_and_limit.py) checks the Eulerian angles for n = 3, …, 17 and their limit.

## 6. Limits of this record.

This record does not cover:

- the identification of the triangular density;
- the principal-root formulation;
- the stability inequality;
- the numerical decimal evaluation of the minimum angle, which is certified in Arb only (Section 4);
- the additional period-two disc derivation;
- the catenoidal reconstruction section;
- the conjecture on optimal remainder constants.

A conjecture is not a verified theorem.

## 7. Other repository evidence.

The following earlier workflow runs concern parts of manuscript 15. Each has its own scope, and the list does not claim that every extension of the article is certified.

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

## References.

1. F. Johansson, Arb: efficient arbitrary-precision midpoint-radius interval arithmetic, *IEEE Trans. Comput.* **66** (2017), no. 8, 1281–92. https://doi.org/10.1109/TC.2017.2690633.
2. The mathlib Community, The Lean mathematical library, in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, New York, 2020, 367–81. https://doi.org/10.1145/3372885.3373824.
3. L. de Moura and S. Ullrich, The Lean 4 theorem prover and programming language, in *Automated Deduction – CADE 28*, A. Platzer and G. Sutcliffe (eds.), Lecture Notes in Computer Science **12699**, Springer, Cham, 2021, 625–35. eISBN 9783030798765. https://doi.org/10.1007/978-3-030-79876-5_37.
