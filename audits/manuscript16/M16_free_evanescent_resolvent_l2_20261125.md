# M16 v16.5 §14.1, Theorem 14.1: the free evanescent resolvent as an operator on `L²(ℝ)` — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/FreeEvanescentResolvent20261125.lean` (44 audited theorems; imports Mathlib only).

## Starting point

`audits/manuscript16/v16.5_section14_free_evanescent_resolvent_norm_20261117.md` (#355) states, for
`κ ∈ ℝ²`, `k > 0`, `|κ| > k`, `α² = |κ|² − k²`, that `R_κ(k²) = (H_κ − k²)⁻¹`, `H_κ = −d²/dz² + |κ|²`,
satisfies `‖R_κ(k²)‖_{L²→L²} = 1/α²`, is self-adjoint and positive with `Im ⟨f, R_κ(k²) f⟩ = 0`, and obeys
`R_κ(k₁²) − R_κ(k₂²) = (k₁² − k₂²) R_κ(k₁²) R_κ(k₂²)`, and lists five Lean obligations, none discharged.
`audits/manuscript16_v165/H2_Bessel_resolvent_domain_20261117.md` (#358) lists the `L² → H²` obligations.
In `main`, `V165ResolventMultiplier.lean` and `V165TwoParameterResolvent.lean` (#361–#364) contain only
the scalar inequalities and the scalar resolvent identity of the multiplier; no Lean statement about an
operator on `L²(ℝ)` exists. No open PR treats §14.1 (checked 25 Nov 2026, 02:55 UTC: the open M16 PRs
#597–#601 concern §14.5; the other open PRs concern M11–M14 and `SpecialImaginaryPoint`, #474).

## What is proved

Mathlib convention `𝓕 f(ξ) = ∫ e^{−2πixξ} f(x) dx`; symbol of `−d²/dz² + b` is `4π²ξ² + b`.
`fourierL2 = Lp.fourierTransformₗᵢ ℝ ℂ` is Mathlib's unitary Fourier transform on `L²(ℝ)` (Plancherel).

| Declaration | Statement |
|---|---|
| `mulOp`, `mulOp_coeFn` | multiplication by `(4π²ξ² + b)⁻¹` on `L²(ℝ; ℂ)` as a bounded operator (Mathlib `holderL`, `L^∞ × L² → L²`) |
| `norm_mulOp` | `‖mulOp b‖ = b⁻¹`: upper bound pointwise; lower bound with the frequency indicators of `[−δ, δ]` and `δ → 0⁺` (no pointwise evaluation at `ξ = 0`) |
| `inner_mulOp_left`, `inner_self_mulOp`, `mulOp_injective`, `mulOp_sub_mulOp` | symmetry, `⟪f, M f⟫ = ∫ (4π²ξ²+b)⁻¹ |f|²`, injectivity, `M(b₁) − M(b₂) = (b₂ − b₁) M(b₁) M(b₂)` |
| `resolvent`, `resolvent_apply` | `R(b) = 𝓕⁻¹ ∘ mulOp b ∘ 𝓕` on `L²(ℝ)` |
| `norm_resolvent` | **`‖R(b)‖_{L²→L²} = b⁻¹`** |
| `resolvent_isSelfAdjoint`, `resolvent_isPositive` | `R(b)` self-adjoint and positive (Mathlib `IsSelfAdjoint`, `ContinuousLinearMap.IsPositive`) |
| `inner_self_resolvent`, `re_inner_self_resolvent_nonneg`, `im_inner_self_resolvent` | `⟪f, R f⟫ = ∫ (4π²ξ²+b)⁻¹ |𝓕f(ξ)|² dξ ∈ ℝ`, `≥ 0`, `Im ⟪f, R f⟫ = 0` for every `f ∈ L²` |
| `resolvent_injective` | `R(b)` injective |
| `resolvent_sub_resolvent` | `R(b₁) − R(b₂) = (b₂ − b₁) R(b₁) R(b₂)` |
| `evanescentOp`, `evanescentOp_apply` | `(evanescentOp b u)(z) = −u''(z) + b u(z)` on `𝓢(ℝ; ℂ)` |
| `fourier_lineDerivOp_one`, `fourier_evanescentOp` | `𝓕(u')(ξ) = 2πiξ 𝓕u(ξ)`, `𝓕(−u'' + bu)(ξ) = (4π²ξ² + b) 𝓕u(ξ)` (Mathlib `SchwartzMap.fourier_lineDerivOp_eq`) |
| `resolvent_evanescentOp` | `R(b)(−u'' + bu) = u` for every Schwartz `u` |
| `alphaSq`, `alphaSq_pos`, `freeEvanescentResolvent` | `α² = ‖κ‖² − k² > 0` for `κ ∈ EuclideanSpace ℝ (Fin 2)`, `0 < k < ‖κ‖`; `R_κ(k²) = R(α²)` |
| `thm14_1_norm` | **`‖R_κ(k²)‖ = 1/(|κ|² − k²)`** |
| `thm14_1_isPositive`, `thm14_1_im_inner`, `thm14_1_injective` | self-adjoint and positive; `Im ⟪f, R_κ(k²) f⟫ = 0`; injective |
| `thm14_1_resolvent_identity` | **`R_κ(k₁²) − R_κ(k₂²) = (k₁² − k₂²) R_κ(k₁²) R_κ(k₂²)`**, `0 < k₁, k₂ < |κ|` |
| `thm14_1_inverse_on_schwartz` | `R_κ(k²)(−u'' + (|κ|² − k²)u) = u` for every Schwartz `u` |

Obligations of #355 discharged: (2) operator-norm equality with the lower bound by Fourier supports near
`ξ = 0`; (4) the real quadratic-form statement `Im ⟪f, Rf⟫ = 0`, separated from any kernel statement;
(5) Lean CI and `#print axioms` on the exact head. The resolvent identity of the note is proved at
operator level.

## Not claimed

- The self-adjoint realisation of `H_κ` on `H²(ℝ)` and `R = (H_κ − k²)⁻¹` on that whole domain (#355
  obligation (1), #358 obligations 1–4). The inverse identity is proved on the Schwartz core only. Mathlib at
  the pinned commit does contain Sobolev (Bessel potential) spaces (`TemperedDistribution.MemSobolev`,
  `BesselPotentialSpace`); the `H²` statement through them is the next step and
  is not done here.
- The Green kernel `e^{−α|z−z'|}/(2α)` (#355 obligation (3)).
- Any Maxwell boundary realisation, trace-class or Schatten statement.
- The match of the parameters and displays with the printed Theorem 14.1 of the current `16.tex` still has to
  be checked against the source, which was not available to this run.

## Verification

Local (pinned toolchain): exit 0, no message from the file; 44/44 theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`. Source SHA-256 recorded in the PR body and in the CI artifact.
Certifying run: `.github/workflows/m16-free-evanescent-resolvent-l2-20261125.yml` (exact-HEAD checkout,
pinned toolchain and Mathlib, failure on any warning, `Try this` or non-standard axiom, `#print axioms`
audit of 44/44 theorems, artifacts).
