# Certification package — Eulerian polar curve manuscript (V478)

Companion to R. Alfano, *Sharp Fourier truncation and limaçon of Pascal approximation of the
Eulerian polar curve* (manuscript V478). Equation and statement numbers refer to the compiled
V478 PDF.

Everything here was produced from scratch, independently of earlier certification files.
There are two layers:

* **`numerics/`**: rigorous interval certificates for every decimal printed in V478, plus
  non-rigorous high-precision cross-checks and symbolic checks.
* **`lean/`**: a Lean 4 + Mathlib formalisation of the abstract core of §§3.2–3.10, of the
  exact-integer comparison of Remark 3.16 and of its crossing-order bracket. **It is
  machine-checked; see §5.**

A decimal printed as `≈ d` is **certified** when a rigorous enclosure `[L, U]` of the exact quantity
lies strictly inside the rounding cell of `d` (the manuscript's criterion, §2). A value printed
as `d…` is certified when `[L, U] ⊂ [d, d + 10⁻ᵏ)`. All final comparisons are exact: interval
endpoints are converted to Python `Fraction`s.

## 1. Interval arithmetic used

| Backend | File | Description |
| --- | --- | --- |
| `mpmath.iv` | (library) | Outward-rounded interval arithmetic of mpmath (pure Python), 70–150 significant digits. |
| `ia_fixed` | `numerics/ia_fixed.py` | Written for this package; independent of mpmath. Exact Python integers, 560-bit fixed point, every rounding directed outward; sin/cos by Taylor series with explicit tail bounds; π by Machin's formula with explicit tail bounds. No floating point. |

Every interval certificate in the table below is run on **both** backends; the integer and symbolic checks need no interval arithmetic.

## 2. Claim → certificate map (V478 numbering)

| V478 claim | Script(s) | Method | Log(s) | Result |
| --- | --- | --- | --- | --- |
| Eq. (6) A₀; Eqs (27)–(28) b_E, a_E (24 dp); Eq. (29) and Cor. 3.9 b_E − a_E − 2/π (20 dp; the former 80-dp value is also checked); Eq. (47) RMS; Eq. (48) 13.315…%; Table 1; Eq. (33) ϑ_E in degrees; "0.0847669…" in the discussion after Thm 3.13 | `si_enclosure.py`, `si_enclosure_fx.py` | Si power series with alternating-tail bound; arctan series with tail bound | `si_enclosure.log`, `si_enclosure_fx.log` | all certified on both backends |
| Eq. (50) D_κ (24 dp); curve lengths 5.5510… and 5.5243… after Eq. (50) | `dkappa_cert.py mp`, `dkappa_cert.py fx` | validated Taylor integration (order 30, 56 steps) of the arclength-matching ODE φ′ = (L_L/L_E) σ_E(θ)/σ_L(φ), with Picard a-priori enclosure and Lagrange remainders; quadrature of (κ_E − κ_L(φ))² σ_E | `dkappa_cert_mp.log`, `dkappa_cert_fx.log` | certified on both backends; enclosure widths ≈ 1.2·10⁻³⁸ and 1.6·10⁻³⁸. **Note:** the draft printed the Eulerian length as 5.5511…, which is the rounded value (2L_E = 5.55107…); V478 now prints 5.5510… |
| h_* to 80 dp (the 80-place decimal is stored in `hstar_certificate.json`); hence Eq. (70) h_* to 20 dp | `hstar_cert.py certify`, `hstar_cert.py replay` | Q(L) > L: supporting-line witness. Q(U) < U: concavity outside θ ∈ [1.98, 2.22], and an adaptive dyadic cover of [1.98, 2.22] by 315 panels (max depth 129) with second-order Taylor bounds. The cover is stored in `hstar_certificate.json` and replayed with `ia_fixed` | `hstar_certify.log`, `hstar_replay.log` | certified (margin for Q(L) > L: 1.344·10⁻⁸⁰) |
| (negative control for h_*) | `hstar_negative_controls.py` | same machinery with the decimal shifted by ±10⁻⁸⁰ | `hstar_negative_controls.log` | the corresponding test fails, as it must |
| Eq. (59) θ_*; Eq. (60) Δ, ε_rad; Eq. (61) b_rad; Eq. (70) h_*, b_H (20 dp); Eq. (71) h_* < ε_rad and b_H > 2a_H > 0; the 0.94 % and "about 42 %" gains; h_* = 0.0492979… and ε_rad = 0.0497667… in the abstract and §1 | `epsrad_cert.py` | interval sign change of f′(cos θ) − m (monotone by Eqs (62)–(64)) brackets θ_*; Δ = g(θ_*) enclosed on the bracket; h_* from the certificate above | `epsrad_cert.log` | all certified on both backends. **Note:** the draft printed ε_rad ≈ …17903, a truncation that fails the rounding-cell criterion; V478 now prints …17904. The old value is kept as a negative control, and it fails. |
| Remark 3.16, Eq. (91): c₆₆₉ = 3.13914926973… < 333/106, 355/113 < c₆₇₁ = 3.14377888960…; c₃ = c₅ = 1/2; c_n strictly increasing for odd 5 ≤ n ≤ 1001 (so the crossing is unique there) | `eulerian_bracket.py` | exact integer recurrence for E(n,k), n ≤ 1001, exact rational comparisons | `eulerian_bracket.log` | correct |
| Lemma 3.15, Eq. (81), two-term expansion c_n = √(π(n+1)/216)(1 + 15/(4(n+1)) + O(n⁻²)), and the crossing order of Remark 3.16: 670 < 216π − 15/2 < 672, while the one-term estimate 216π exceeds 672 | `lemma315_asymptotic.py` | (i) exact rational c_n for odd n ≤ 1001 from the Eulerian recurrence; (n+1)(c_n/√(π(n+1)/216) − 1) tabulated against 15/4. (ii) the two inequalities on both interval backends and from 333/106 < π < 355/113 | `lemma315_asymptotic.log` | (i) 3.7539… at n = 669, 3.7526… at n = 1001, strictly decreasing for odd 101 ≤ n ≤ 1001 (a corroboration; the expansion itself is proved in V478, Lemma 3.15). (ii) certified: 671.066 < 216π − 15/2 < 671.085; also proved in Lean (`Crossing`) |
| §3.11, Montgomery–Taylor: C_MT = 1/2 + z₀ coth z₀ = 1.3274992963… and 3/2 − z₀ coth z₀ = 0.6725007…, z₀ = i/√2 | `montgomery_taylor.py`; Lean `MontgomeryTaylor.z0_coth_z0` | (1/√2) cot(1/√2) enclosed on both backends; the identity z₀ coth z₀ = (1/√2) cot(1/√2) proved in Lean | `montgomery_taylor.log` | certified on both backends |
| Symbolic identities: Eq. (4); r_E′ (proof of Prop. 3.6); Eq. (40); Cor. 3.8 numerator; Eqs (59), (62)–(64); det JᵀJ = n + 1 (Lemma 3.14); B(eʰ) = e^{h/2}Z(h), r_E(t) = Z(it), ψ″(0) = 1/12, −iψ′(iπ) = 1/π and the Gaussian homothety (§3.11) | `symbolic_checks.py` (sympy) | exact symbolic simplification | `symbolic_checks.log` | all hold |
| Cross-checks (non-rigorous, 45–120 digits) | `constants.py`, `limacon_minimax.py`, `dkappa.py` | mpmath quadrature / Newton | `*.log` | agree with every printed digit |

## 3. How the h_* certificate proves Eq. (70)

The manuscript proves (proof of Thm 3.13) that Q(h) − h is strictly decreasing and vanishes exactly
at h_*. Hence Q(L) > L and Q(U) < U imply L < h_* < U (formalised in Lean as
`EulerianCert.Limacon.balance_bracket`). With d the 80-place decimal, L = d − ½·10⁻⁸⁰ and
U = d + ½·10⁻⁸⁰, so d is h_* correctly rounded to 80 places, and the 20-place value of Eq. (70)
follows (`epsrad_cert.py`).

* **Q(L) > L.** Take exact rational parameters θ₀ (on Γ_E) and t₀ (on ∂Ω_L) near the critical
  pair. The outward normal half-plane at γ_L(t₀) contains the convex body Ω_L, which is convex
  because c + L > 2m. Hence dist(γ_E(θ₀), Ω_L) ≥ N·(γ_E(θ₀) − γ_L(t₀))/|N| > L.
* **Q(U) < U.** By the symmetry y ↦ −y it suffices to take θ ∈ [0, π].
  * Outside [1.98, 2.22]: dist ≤ max(0, g(cos θ) − U), where g = f − ℓ is concave
    (Eqs 62–64), and g(cos 1.98), g(cos 2.22) < 2U < g(cos 2.1).
  * On [1.98, 2.22]: each panel uses the path t(θ) = t_c + s(θ − θ_c) and
    F(θ) = |γ_E(θ) − γ_U(t(θ))|² ≥ dist². The bound F(θ_c) + |F′(θ_c)|w + ½ sup|F″| w² < U² is
    checked in interval arithmetic. t_c and s are arbitrary recorded decimals: any choice gives a
    valid upper bound.

## 4. What the numerical layer relies on

The certificates evaluate closed forms and characterisations that the manuscript proves:

* the Si formulas for A₀, b_E, a_E and the energy (Prop. 3.1, §3.7);
* the equioscillation characterisation of θ_*, Δ and ε_rad (Thm 3.12);
* the scalar-balance characterisation of h_* (Thm 3.13);
* the arclength-matching reduction for D_κ (header of `dkappa_cert.py`).

The certificates make these evaluations rigorous; they do not re-prove the characterisations.
Lean (§5) covers the algebraic and order-theoretic steps of those proofs that are listed there.

## 5. Lean formalisation (`lean/`)

**Status: machine-checked (3 October 2026).** `lake build` completes with no errors and no `sorry`.
The main results depend only on Lean's standard axioms `propext`, `Classical.choice` and
`Quot.sound`; the kernel computations use only `propext`. No `native_decide` is used, so the
compiler is not trusted. The full axiom report is in `lean/logs/axioms.log` (produced by
`lean/AxiomCheck.lean`), and the build log is `lean/logs/lake_build.log`.

* Toolchain: Lean `v4.35.0-rc3` (`lean-toolchain`).
* Mathlib: commit `0272bbe1c093d038d7257ab15306abd58245f9ff`.
* Build: `lake exe cache get && lake build`. Without the cache, `lake build` compiles the required
  part of Mathlib from source (about 2 400 files).
* Check: `lake env lean AxiomCheck.lean`.
* Cost of `EulerianCert` itself: 2–3 minutes, of which 110–160 s is the kernel evaluation in
  `Bracket`. Peak memory is about 4.5 GB.
* The only messages are 23 advisories that the files import Mathlib modules "designed for use with
  the module system". They are not warnings about the proofs.

| Module | V478 content | Main declarations |
| --- | --- | --- |
| `SignCriterion` | **Lemma 3.2** in full, for 0 ≤ d_n ≤ c_n, ∑ c_n < b: positivity, minima at π, f_c(π) = q, f_d(π) = q + E, sharp sup-norm error E, and **exact Hausdorff distance E** between the polar curves as subsets of ℂ. Its truncation case (abstract form of Cors 3.3, 3.9 and Prop. 3.4) and damping case (Cor. 3.11) | `common_endpoint_sign_criterion`, `sign_criterion`, `damping` |
| `Bracket` | **Remark 3.16, Eq. (91)**. Eulerian numbers E(n,k) (Deza's convention of §2, 0 ≤ k ≤ n − 1) are defined by a one-pass row recurrence and proved to satisfy E(1,0) = 1, E(n,k) = 0 for k ≥ n, E(m+1,0) = E(m,0) and E(m+1,k) = (k+1)E(m,k) + (m+1−k)E(m,k−1); these facts determine the triangle. Kernel evaluation (`decide +kernel`) gives 106·669! < 333·670·(E(669,334) − E(669,333)) and 355·672·(E(671,335) − E(671,334)) < 113·671!, i.e. c₆₆₉ < 333/106 and 355/113 < c₆₇₁ with c_n = n!/((n+1)(E(n,(n−1)/2) − E(n,(n−3)/2))), positivity of both differences and the row sums 669!, 671!. With 333/106 < π < 355/113 this gives α₆₇₁ < ϑ_E < α₆₆₉ | `E_succ`, `c669_lt`, `c671_gt`, `angle_bracket` |
| `Crossing` | **Remark 3.16**, crossing order: 670 < 216π − 15/2 < 672 (the two-term estimate lies inside the bracket of Eq. (91)) and 672 < 216π (the one-term estimate does not), from Mathlib's bounds 3.14 < π < 3.1416 | `crossing_bracket`, `one_term_outside` |
| `Limacon` | **Cor. 3.8** (numerator b² + 3ab cos θ + 2a², its minimum, b_E > 2/π > 32/(3π³) > 2a_E). **Thm 3.12**: c − 2m = 3/π − 1/2 > 0 and the three-point uniqueness. **Thm 3.13**: endpoint containment (73)–(74), its strict and equality cases, and the scalar-balance lemmas (uniqueness of h_*, D ≥ h_*, the certificate logic L < h_* < U, and h_* < ε_rad from Q(ε_rad) < ε_rad) | `convexity_chain`, `affine_unique`, `endpoint_containment(_strict)`, `endpoint_equalities`, `balance_bracket`, `balance_lt` |
| `Corner` | **Props 3.6–3.7**: r_E′, r_E″, r_E(π) = 2/π, r_E′(π) = −2/π² (31), one-sided tangents (32), tan(ϑ_E/2) = 1/π (33), unit tangents (36), Sullivan atom (38) with norm 2 sin(ϑ_E/2), and Eq. (40) with its positivity | `curvature_numerator_pos`, `tangent_minus`, `tangent_plus`, `sullivan_atom` |
| `Combinatorics` | Eq. (21) (telescoping identity, and the strict tail bound from the strict termwise bound of Eq. (9)); Lemma 3.14 (JᵀJ = I + 𝟙𝟙ᵀ, det = n + 1); Gaussian homothety of §3.11 | `tail_bound_strict`, `det_JtJ`, `gaussian_homothety` |
| `MontgomeryTaylor` | §3.11: z₀ coth z₀ = (1/√2) cot(1/√2) for z₀ = i/√2 of Eq. (4), hence C_MT = 1/2 + z₀ coth z₀ and 3/2 − z₀ coth z₀ in the (1/√2)cot(1/√2) form of Lamzouri (arXiv:2609.02882v2, Eqs. (1.1), (3.1)) | `coth_imaginary`, `z0_coth_z0` |

**How the abstract statements apply.** `SignCriterion` works with an arbitrary non-negative
summable coefficient sequence. Taking c_n = |A_n| uses the sign pattern and summability of
Prop. 3.1, together with the identity f_c = r_E (Fejér). These are proved in the manuscript, not
in Lean. Likewise `Limacon` and `Corner` take as hypotheses the inputs that come from analysis
outside their scope, for example the bounds on a_E, b_E and the antitonicity of Q.

**Not formalised:**
* the Fourier coefficient formulas and signs of Prop. 3.1 (Mathlib has no convenient sine-integral
  API) and the identification of r_E with its Fourier series;
* Prop. 3.10 (Lebesgue-constant growth);
* the nearest-point geometry of Thm 3.13 and the turning-tangent and measure statements of Prop. 3.7;
* the volume and local-limit statements of §3.11, the Fourier inversion formula after Eq. (78) and
  the Laplace-method expansion of c_n in Lemma 3.15;
* the combinatorial meaning of E(n,k) (permutations with k ascents), which is classical.

## 6. Reproducing

**Numerics.** Python ≥ 3.12 with mpmath (tested on commit
`90b16c8ea4d9edef6f8e91acd1723651098f24c0`) and sympy (commit
`f6d8906c03eec71d4cbbe0275722a7915d965a97`). `ia_fixed.py` needs nothing but the Python standard
library.

```
cd numerics
python3 si_enclosure.py ; python3 si_enclosure_fx.py
python3 dkappa_cert.py mp ; python3 dkappa_cert.py fx
python3 hstar_cert.py certify ; python3 hstar_cert.py replay
python3 hstar_negative_controls.py
python3 epsrad_cert.py
python3 eulerian_bracket.py
python3 lemma315_asymptotic.py
python3 montgomery_taylor.py
python3 v500_certificates.py      # companion manuscript V500, Section 7
python3 symbolic_checks.py
```
If mpmath is not installed system-wide, put its source checkout on the path, e.g.
`PYTHONPATH=/path/to/mpmath python3 lemma315_asymptotic.py`.
Total running time on 2 cores: about 7 minutes, mostly the two D_κ runs.

**Lean.**
```
cd lean
lake exe cache get      # optional: downloads compiled Mathlib
lake build
lake env lean AxiomCheck.lean
```

## 7. Companion manuscript V500 (cyclohedral zeta targets, Chebyshev strong cycles)

R. Alfano, *Cyclohedral zeta targets, Cassini spectral bridges, and Chebyshev strong-cycle
realisations* (manuscript V500). Numbers refer to the V500 PDF. The same two layers are used.

| V500 claim | Certificate | Method | Result |
| --- | --- | --- | --- |
| Cor. 3.1, Eqs. (24), (28)-(35): branch in the right half-plane on \|q\| < 1/4, factorisation (ω-1)²(ω+2), closed form 8(ω+2)/(ω(ω+1)²), value 6 at q = 0, zero-free property | Lean `Cyclohedral.branch_right_half_plane`, `tail_numerator_factor`, `zhat_closed_form`, `zhat_at_origin`, `zhat_zero_free` | Mathlib, `field_simp`/`ring` | proved |
| Cor. 3.1, Eqs. (15)-(18): Taylor coefficients of the closed form are C(2m+4, m+2) | `v500_certificates.py` [A] | exact power series, m ≤ 300 | correct |
| Eq. (76): T₂(ω) = 1 − 8q when ω² = 1 − 4q | Lean `cyclohedral_spectral_link` | Mathlib `Chebyshev.T` | proved |
| §4.3 after Eq. (76): ω maps ∂D_q onto the right loop of \|ω² − 1\| = 1, the lemniscate √2·K_{1/2}, sending q = 1/4 to its node; the circles \|w\| = 1 and \|w − 1\| = 2 meet only at w = −1 | Lean `boundary_lemniscate`, `lemniscate_scaling`, `node_iff`, `circles_tangent` | Mathlib, norms in ℂ | proved |
| Prop. 4.1, Eqs. (55)-(56): det[ξI − A_c(θ)] = ξ² − 1/2 − c e^{iθ} and the chain with T₂ and 𝒬 | Lean `charpoly_A`, `cassini_chain` | `Matrix.det_fin_two` | proved |
| Eq. (58): M₂(e^{iθ}) = A_{1/2}(θ)ᵀ | Lean `M2_eq_A_half_transpose` | cos(π/4) = 1/√2, 2^{-1/2} = 1/√2 | proved |
| Prop. 4.2, Eq. (65): det[λI − Mₙ(w)] = 2^{1−n}[Tₙ(λ) − w] | `v500_certificates.py` [F] | interval determinant, n = 2..12 | the difference encloses 0 (consistency check; the proof is a one-permutation expansion) |
| Cor. 4.5: T_{ab} = T_a ∘ T_b = T_b ∘ T_a; T_{2m} ∓ 1 factorisations behind (82)-(83) | Lean `cheb_composition`, `cheb_even_factorisations` | Mathlib `Chebyshev.T_mul` | proved |
| Prop. 4.6, Eqs. (93), (95) and the node-count check, Eqs. (97)-(99): both counts give ⌊(n−1)²/2⌋ | Lean `riemann_hurwitz_genus`, `node_count_genus`; `v500_certificates.py` [D] | integer arithmetic, all n | proved |
| Prop. 4.6: monodromy group D_n of order 2n | `v500_certificates.py` [G] | numerical continuation, n = 3..6 | order 2n (non-rigorous cross-check) |
| Cor. 4.7, Eqs. (102)-(104), and the Floquet identity after it | `v500_certificates.py` [B] | exact arithmetic in ℚ(√2)(i), n ≤ 12 | correct |
| Eqs. (89)-(90): dyadic product, Viète's 2/π, radial-mean series | `v500_certificates.py` [C] | enclosures with explicit tail bounds, both backends | enclosures agree (widths ≤ 10⁻³⁶) |
| Figure 1: the disc of radius 11/50 about 3/4 + 57i/4 lies in the strip and misses ρ₁ | `v500_certificates.py` [E] | exact rationals, with 14.1347251417 < γ₁ < 14.1347251418 | distance > 0.2752 > 0.22 |

Not formalised: Voronin universality and the zeta-jet corollary (classical theorem applied to the
certified target), Brualdi localisation, cyclicity and the Jordan structure of Cor. 4.5, and the
covering-space part of Prop. 4.6.

## 8. Figure: Eulerian distributions, n = 3, …, 670

`figures/eulerian_distribution_FS_IX14/` holds a vector PDF of the Eulerian distributions for
n = 3, …, 670 in the field of Flajolet–Sedgewick Figure IX.14, the script that writes it from the
book's formulas, and a one-page description.

## 9. License

All files in this repository are released under CC0 1.0 Universal (see `LICENSE`).
