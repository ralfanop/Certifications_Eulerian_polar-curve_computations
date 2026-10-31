# Lean 4 certification of manuscript V173: Sections 3, 4, 6, 7, 8, 9.1–9.2, Lemma 5.5, Appendix A and the decimal values

Toolchain: Lean 4.24.0 with Mathlib `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`. This is the EulerianGrothendieck project with the new `Bridge` library declared in `lakefile.toml`.

Build:

```
lake build Bridge
lake env lean Scratch/Audit.lean
```

Audit result: 821 theorems in the namespace `EulerianBridge` (`lake env lean AuditBridge.lean`), none of which uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`. No `sorry`.

## Cited published results (explicit hypotheses, not re-proved)

| Hypothesis (Lean) | Source | Used for |
|---|---|---|
| `Isoclinic.VourdasOverlap` | Vourdas, Ann. Physics 482 (2025), Lemma 4.1, Eq. (52) | Prop. 9.1 |
| `hV : 𝒱†𝒱 = I` in `StepFrame.frame_factorisation` | Hall, Thm. 14.18 | Prop. 3.6 |
| `hM : M M† = I` in `StepFrame.frame_factorisation` | Vourdas, Lemma 4.1 | Prop. 3.6 |
| `Hall.MelzakProduct` | Melzak (1961), p. 39 (2) | Prop. 3.5, Melzak product |
| `PW.Plancherel` | Plancherel theorem, convention (22), band-limited case | Prop. 3.1 (17), Thm. 3.10, Cor. 3.11 |
| `Malmsten.Blagouchine` | Blagouchine, Ramanujan J. 35 (2014), p. 33, Eq. (16) | Prop. 7.1 |
| `hA` in `Malmsten.catalan_q`, `MalmstenIBP.catalan_both` | Abdulsalam (2025), value of (104) | (104)–(105) |
| `MellinExtras.SechFourier` | Gradshteyn–Ryzhik 3.981.3 | Prop. 6.6 |
| `Rabotnov.EkerEceCriterion` | Eker–Ece, Hacet. J. Math. Stat. 51 (2022), Thm. 2.8 | Prop. 8.1, convexity |

## Statements certified

**Section 3** (`Fock3`, `Fock3b`, `Fock3c`, `Hall`, `FrameBridge`, `StepFrame`, `Ladder`–`Ladder5`, `PaleyWiener`, `PaleyWiener2`, `PaleyWiener3`, `PaleyWiener4`)
- Prop. 3.1:
  - ‖ψ_L‖ = 1: `psiL_norm`;
  - (16): `momentum_psiL`;
  - (17), via Plancherel: `PW.momentum_normalisation`.
- Prop. 3.2:
  - (9): `rE_kernel`, `GE_kernel`, `kernel_point`;
  - r_E and G_E are entire: `rE_differentiable`, `GE_differentiable`;
  - r_E, G_E ∈ L²(μ_α): `memLp_rE`, `memLp_GE`;
  - the bounds (10): `fock_upper`;
  - convergence in the Hilbert-space norm:
    - t ↦ k_t ∈ L²(μ_α) is continuous: `continuous_kvec`, `inner_kvec`;
    - the Bochner integrals equal r_E and G_E in L²(μ_α): `bochner_rE`, `bochner_GE`.
- Prop. 3.3:
  - (11): `fock_norm_rE` (double integral), `fock_norm_series` (series), `fock_norm_GE`;
  - (12): `AppendixA.m_eq`, `odd_moment`;
  - (21): `fock_norm_Shi`, giving 4α ∫₀^{1/2} sinh(t/2α)/t dt = 4α Shi(1/(4α)).
- Prop. 3.4, (13)–(15): `hall_uħ`, `segal_result`.
- Prop. 3.5:
  - `hall_one`;
  - C_B = r_E(1)/(𝒱₁u₁)(i/√2): `CB_eq`;
  - the factorisation: `isolated_profile`;
  - Melzak form: `CB_melzak`;
  - decimal value: `Decimals.bargmann_constant_value`.
- Prop. 3.6 (the step-function isometry U_d):
  - orthonormality: `orthonormal_v`;
  - U_d†U_d = I: `U_adj_U`;
  - U_d c_d = ψ₁: `U_c`;
  - (34)–(36) and the two orthogonal projections: `frame_factorisation`.
- Prop. 3.8 (polyanalytic ladder; Wirtinger derivatives defined via the real Fréchet derivative):
  - E₀ = r_E: `E_zero`;
  - (32): `a_E`, `adag_E`;
  - (a†)ⁿ r_E = √(n!) Eₙ: `adag_iter`;
  - exact order n+1 (31): `exact_order`;
  - [a, a†] = I on the ladder: `commutator_E`;
  - Eₙ ∈ L²(μ_α): `memLp_E`;
  - (30): ⟨Eₙ, Eₘ⟩ = 4α δₙₘ Shi(1/(4α)): `inner_E`;
  - orthonormal sequence: `orthonormal_E`;
  - the proof runs through Gaussian integration by parts (`ibp`) and Jₙₘ = δₙₘ n! αⁿ e^{st/α} (`J_closed`).
- Thm. 3.10:
  - r_E ∈ PW: `rE_eq_T`;
  - (24): `KE_eq`, `reproducing`;
  - (25): `norm_rE_sq`;
  - (26): `orthonormal_Φ`, `expansion` (L²(ℝ) completeness of the expansion);
  - (27): `sampling` (pointwise), `sampling_uniform` (uniform on every strip |Im z| ≤ R), `parseval`.
- Cor. 3.11:
  - PW is closed: `PWsub_closed`;
  - P_E² = P_E = P_E*: `PE_idem`, `PE_selfAdjoint`;
  - ‖P_E‖ = 1: `PE_norm`;
  - convolution kernel: `PE_kernel`;
  - absolute convergence: `kernel_integrable`;
  - Fourier multiplier with symbol 1_{[-1/2,1/2]}: `PE_multiplier`;
  - (29): `convolution`.

**Section 4** (`Appell`, `BernoulliAppell`, `Duplication`)
- Formal operators f(D) on K[x] (`Appell.op`):
  - linearity, `op_one`, `op_X`, `op_sub`;
  - multiplicativity `op_mul`, through the Appell property `op_X_pow`;
  - 𝒜 = M(D) with (𝒜p)(x) = ∫₀¹ p(x+t) dt: `op_Mser_integral`.
- Prop. 4.1:
  - (59)–(61): `avg_inverse`, `MnegD_inverse`, `inverse_difference`;
  - B_n = 𝒜⁻¹xⁿ: `op_bernSer_X_pow`;
  - (62): `avg_bernoulli`, `integral_bernoulli`;
  - (63)–(64) through z¹⁰: `bernSer'_coeffs`, `bernSer_coeffs`.
- Thm. 4.2:
  - (65)–(66): `duplication`, `sech_operator`, `Mc_duplication`, `Mc_sech`;
  - (67): `S_eq_sech`;
  - (68): `S_X_pow`;
  - (69): `eulerPoly`;
  - (70): `euler_comparison`.

**Section 5, Lemma 5.5** (`Saddle/*`: the saddlepoint estimate with two derivatives, in its `C²` form)
- Objects as in the manuscript:
  - `w_M` (density of `S_M`, iterated convolution): `Saddle.w`;
  - `g_M(x) = M w_M(Mx)`: `gM`;
  - `A(z) = ∫ e^{zt}`, `Λ = log A`, `κ_r = Λ^{(r)}`: `A`, `Lr`, `κ`;
  - `s = I'` (inverse of `Λ'`): `UL.Ip`, ported from the certified UniformLanczos `Lambda` module (Lemma 5.3);
  - `I(x) = s x − Λ(s)`: `Irate`, which equals `sup_t (tx − Λ(t))` (eq. (56)): `Irate_isGreatest`;
  - `v = Λ''(s)`: `vx`;
  - `η = (κ₄/v² − 5κ₃²/(3v³))/8` (eq. (67)): `etaS`, `etaX`.
- Representation (69)–(70):
  - Laplace transform `∫ e^{zy} w_M = A(z)^M`: `laplace_w`;
  - Fourier inversion of the tilted density, `w_M(y) = (2π)⁻¹ ∫ A(s+iu)^M e^{−(s+iu)y} du` for every real tilt `s`: `w_eq_Wint`;
  - the first two derivatives under the integral sign: `deriv_w_ofReal`, `deriv2_w_ofReal`, `w_repr`.
- Bounds on `χ`:
  - `|χ| ≤ 1`, and `|χ| ≤ ρ < 1` for `|u| ≥ δ` uniformly in `|s| ≤ σ` (eq. (72)): `norm_χ_le_one`, `exists_rho`;
  - decay (69): `norm_A_decay`.
- Inner region, expansion (73) and (76) carried to fourth order with a fifth-order remainder:
  - Taylor expansion with Cauchy estimates, uniform in the tilt: `taylor_Lc`, `coeff_bound`, `Ψ_taylor`;
  - pointwise bound: `inner_pointwise`;
  - Gaussian moments: `integral_complex_moment`;
  - `I_r = √(2π/v)(N_r(ε) + O(ε⁵))`, `r = 0, 1, 2`: `Ir_expansion`.
- Cancellations (74) and the coefficients of (77): `id_G02` (`= η`), `id_G11`, `id_G13`, `id_G22`, `id_G24`.
- Eq. (68) with explicit derivatives:
  - `lemma_5_5`: for every `b ∈ (0, 1/2)` there are `M₀` and `C` with `|E_M|`, `|E_M'|`, `|E_M''| ≤ C/(M√M)` on `[−b, b]`, together with `HasDerivAt` for `E_M` and `E_M'`;
  - `lemma_5_5_C2`: `E_M''` is continuous on `[−b, b]` for `M` large.
- The consequences stated after (68):
  - `lemma_5_5_phi`: `|φ_M' − I'| ≤ C/M` and `|φ_M'' − I''| ≤ C/M` on `[−b, b]`, with `I'' = 1/v`, and `sup |φ_M''| ≤ C`.
- The proof route differs from the printed one only in one point. The printed proof differentiates the tilted integral `𝒥_M(x)` in `x`. Here the tilt `s` is held fixed while differentiating in `y = Mx`, and only then is `s = s(x)` set; the representation holds for every real `s`. This uses the expansions of `∫ (iu)^r χ^M du` up to `O(ε⁵)` with `ε = M^{−1/2}`, and the identities `id_G22`, `id_G24` provide the cancellation of the leading terms. The statement certified is (68) exactly as printed.

**Section 6** (`Mellin`, `MellinExtras`)
- Def. 6.1 and Prop. 6.2: `qE_eq_sech`, `qE_pos`, `qE_strictAntiOn`, `qE_le_exp`.
- Thm. 6.3:
  - transforms: `mellin_sech`, `mellin_sech_sq`;
  - (94): `moment_one`, `moment_two`, `moment_three_sq`;
  - values: `dirichletBeta_three`, `dirichletEta_three`, `odd_cube_sum`.
- Cor. 6.4: `beta_three_polygamma`, `det_mellin`, `radius_mellin`.
- Cor. 6.5: `two_constants`.
- Prop. 6.6: `qE_characteristic`, `integral_ρ`, `qE_posDef`.

**Section 7** (`Malmsten`, `MalmstenIBP`)
- Prop. 7.1: `kernel_eq_qE`, `T_eq_qE`, `T_eq_log`, `T_I2_dE`.
- (104), first equality by integration by parts: `catalan_ibp`.
- (104)–(105) with the cited value: `catalan_both`.

**Section 8** (`Rabotnov`, `MellinExtras`)
- F_E(w²) = 2w sinh(w/2): `FE_sq`.
- F_E(w²) = w² r_E(iw): `FE_eq_rE`.
- F_E is entire: `FE_differentiable`.
- Rabotnov coefficients: `c_eq_rabotnov`, `FE_eq_rabotnovFun`.
- (107): `FE_pi_sq`, `FE_neg_pi_sq`, `FE_ratio`.
- Convexity, from the cited criterion: `FE_convex`.

**Section 9.1–9.2** (`Isoclinic`, `InverseTangent`)
- Prop. 9.1: `V_isometry`, `overlap_gram`, `trace_P_mul_P`.
- (111)–(112): `sigma_eq`, `two_sigma_one`, `varthetaE_eq`.

**Appendix A** (`AppendixA`, `AppendixAGd`, `AppendixAMoments`)
- The sequence a(k):
  - closed form and identities: `m_eq`, `m_inv`, `a_eq_hypercube_edges`;
  - recurrence (115): `a_rec`;
  - generating functions (113)–(114): `a_ogf`, `a_egf`.
- (116): `moments_sum`, `integral_inv_one_sub_sq`.
- Gudermannian (117):
  - `gd_eq`, `gd_strictMono`, `abs_gd_lt`, `range_gd`;
  - inverse relations: `gdInv_gd`, `gd_gdInv`.
- Lambertian (118): `gdInv_eq_arctanh_sin`, `gdInv_eq_log_tan`.
- Special values (119)–(120): `gdInv_pi_div_four`, `gdInv_arctan_four_thirds`.
- Semifactorial forms (121)–(123): `m_semifactorial`, `central_binom_semifactorial`, `catalan_semifactorial`.
- Moments of the four laws (124)–(127): `uniform_moments`, `arcsine_moment`, `semicircle_moment`, `gaussian_moment`.

**Decimal values** (`Decimals`, `EtaQuarter`)
- The six displayed scalars: `endpoint_value`, `joining_point_value`, `determinant_value`, `beta_three_value`, `angle_degrees_value`, `bargmann_constant_value`.
- η(1/4) ≈ −0.184391: `eta_quarter`.

## Not formalised here

- Statements left to the cited sources:
  - log(1+√2) = √2 L₈(1) (Finch);
  - convex ⇒ starlike (classical);
  - the holomorphic continuation remark after Theorem 6.3.
- Lemma 5.6 uses Floater's B-spline inequality (cited, published); Theorem 5.9 uses Levin–Lubinsky, Theorem 13.4 (cited, published). Both enter the manuscript as published inputs.
