# M16 v16.5 §14.2, Proposition 14.2: Dirichlet and Robin Green operators positive and self-adjoint — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletPositive20261125.lean` (50 audited declarations), SHA-256
`bdfd818ada54b17c72df2a031a06fde742f6c5f8db029cc61a3228924b3e681c`. It imports `Mathlib` and
`Manuscript16.RobinDirichletL2Bounded20261125` (PR #605, head `2a5ec351dc5f5b652fd76caa8411be46eac1032b`,
source SHA-256 `303e9028ae0b34a14e0c02dcd44db48fa4fa5bf4578aa9e8f6b05318db479e4a`), which imports
`Manuscript16.RobinDirichletRankOne20261125` (PR #603, head `0a0022bffded18c25781fec7fa94fa1c8e07d04a`,
source SHA-256 `78663893e197799f53ae47ef4ec670314cf8770982475d6d02746042e6dad6fc`). This branch is stacked
on #605 (and therefore on #603). Nothing of #603 or #605 is re-proved.

## Starting point

#605 realises the Dirichlet and Robin Green kernels of Proposition 14.2 as bounded operators
`KDop`, `KRop = KDop + P_a` on `L² = L²((0,∞); ℂ)` with `KDop f = K_D f`, `KRop f = K_R f` a.e., and
lists as **not claimed** the self-adjointness and positivity of `KDop`, `KRop`. That is the obligation
discharged here. No open PR treats it (checked 25 Nov 2026, 07:00 UTC: #597–#602 concern §14.1 and
§14.5, #603, #604 and #605 state it as not claimed or do not mention it, #474 concerns
`SpecialImaginaryPoint`/M14, the others M11–M14).

The first obligation of the run brief, `thm:dirac-maxwell-obstruction-164` (i)–(ii), is closed in `main`
by #576, #585 and #588 (see the register) and was not re-proved.

## Method: Volterra factorisation of the Dirichlet kernel

With `ψ(z,s) = 1_{s ≤ z} e^{−a(z−s)}`, for `z, w ≥ 0`

`∫₀^∞ ψ(z,s) ψ(w,s) ds = ∫₀^{min(z,w)} e^{−a(z+w)+2as} ds = (e^{−a|z−w|} − e^{−a(z+w)})/(2a) = G_D(z,w)`,

because `z + w − 2 min(z,w) = |z − w|`. Hence `K_D = V W` with the Volterra operators
`(V h)(z) = ∫₀^∞ ψ(z,s) h(s) ds`, `(W f)(s) = ∫₀^∞ ψ(w,s) f(w) dw`, and `V = W†`; therefore
`K_D = W† W ≥ 0`, and `K_R = W† W + P_a ≥ 0` because `P_a ≥ 0` (#603). No spectral theorem, Fourier
transform or self-adjoint realisation is used.

## Statements

Part A — Volterra kernel:

- `psi`, `psi_nonneg`, `psi_le_exp` (`0 ≤ ψ(z,s) ≤ e^{−a|z−s|}`), `abs_psi_le`, `measurable_psi`,
  `psi_mul_psi`.
- **`integral_psi_mul_psi`**: `∫₀^∞ ψ(z,s) ψ(w,s) ds = G_D(z,w)` for `a > 0`, `z, w ≥ 0` (fundamental
  theorem of calculus on `[0, min(z,w)]`).

Part B — Volterra operators:

- `memLp_of_bound_meas`, `memLp_psi_row`, `memLp_psi_col`, `rowVec`, `colVec`, `Vfun`, `Wfun`,
  `Vfun_eq_integral`, `Wfun_eq_integral`.
- Schur bound for kernels dominated by `e^{−a|z−w|}` (reusing `schur_lintegral` of #605):
  `expK`, `measurable_expK`, `expK_symm`, `lintegral_expK_real` (`∫_ℝ e^{−a|z−w|} dw = 2/a`),
  `row_expK`, `col_expK`, `enorm_le_expK`, `lintegral_kernel_sq_le`, `aestronglyMeasurable_kernel`,
  `eLpNorm_kernel_le`, `memLp_kernel`, `norm_toLp_kernel_le`, `abs_psi_swap_le`, `measurable_psi_swap`.
- `Vop`, `Wop : L² →L[ℂ] L²` (`LinearMap.mkContinuous`), with `Vop_ae_eq`, `Wop_ae_eq`,
  `memLp_Vfun`, `memLp_Wfun`, `norm_toLp_Vfun_le`, `norm_toLp_Wfun_le`, `Vfun_add`, `Vfun_smul`,
  `Wfun_add`, `Wfun_smul`.

Part C — adjointness:

- `mul_le_sq_add_sq`, `lintegral_enorm_sq_lt_top`, `integrable_kernel_prod` (integrability of
  `k(z,s) g(s) f(z)` on `(0,∞)²` for `f, g ∈ L²`, by Tonelli and the Schur bound).
- **`inner_Vop`**: `⟪V h, f⟫ = ⟪h, W f⟫` for all `h, f ∈ L²(0,∞)` (Fubini); **`Vop_eq_adjoint`**:
  `V = W†`.

Part D — factorisation:

- `Vfun_Wop`: `V(W f)(z) = (K_D f)(z)` for every `z ≥ 0` (Fubini and Part A).
- `KDop_eq_Vop_comp`: `KDop = V ∘ W`; **`KDop_eq_adjoint_comp`: `KDop = W† ∘ W`** on all of `L²(0,∞)`.

Part E — consequences:

- **`KDop_isPositive`**, **`KDop_isSelfAdjoint`** (Mathlib `ContinuousLinearMap.IsPositive`, `IsSelfAdjoint`).
- **`inner_KDop_self`**: `⟪f, K_D f⟫ = ‖W f‖²`.
- `norm_KDop_eq`: `‖K_D‖ = ‖W‖²` (C*-identity); `norm_Wop_le`: `‖W‖ ≤ a⁻¹`.
- **`KRop_isPositive`**, **`KRop_isSelfAdjoint`** for `β < a` (`K_R = K_D + P_a`, `P_a ≥ 0` from #603).

Manuscript form: `prop14_2_positive` (`κ ∈ EuclideanSpace ℝ (Fin 2)`, `c = ‖κ‖²`, `β > 0`,
`t < c − β²`, `a = √(c − t)`): `K_D = W† W`, `K_R = W† W + P_a`, both positive and self-adjoint,
`⟪f, K_D f⟫ = ‖W f‖²`.

## Not claimed

- The self-adjoint Dirichlet and Robin realisations `H_D`, `H_R` on `H²(0,∞)` and the identification
  `KDop = (H_D − t)⁻¹`, `KRop = (H_R − t)⁻¹`. Positivity of `KDop`, `KRop` is proved for the integral
  operators of the printed kernels, not deduced from a resolvent.
- Strict positivity, injectivity, dense range; the value of `‖K_D‖` (only `‖K_D‖ = ‖W‖²` and the bound
  `≤ a⁻²` of #605).
- Schatten-ideal membership; the essential spectrum; any Maxwell or geometric identification.
- Correspondence with the printed Proposition 14.2 of the current `16.tex` (source not available to
  this run).

## Verification

- Local, pinned toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib
  `0272bbe1c093d038d7257ab15306abd58245f9ff` (checked with `git -C .lake/packages/mathlib rev-parse HEAD`):
  the two imported modules and the new module compile with exit code 0 and **no** message (no error, no
  warning, no `Try this`); `#print axioms` on all 50 declarations of the new module and on the 64 + 29
  declarations of the imported modules reports only `propext`, `Classical.choice`, `Quot.sound`. The
  compile-and-audit step of the workflow was run locally with success. No `sorry`, `admit`, `axiom`,
  `unsafe`, `implemented_by`, `extern`; no `continue-on-error`; no module removed or weakened.
- Certifying run: `.github/workflows/m16-robin-dirichlet-positive-20261125.yml` — checkout of the exact PR
  head, assertion of the head SHA, of the toolchain file and of the Mathlib pin, compilation of the two
  imported modules and of the new module, failure on any error, warning, `Try this`, `sorryAx`,
  `Lean.ofReduceBool` or non-standard axiom, upload of the logs and of `m16-rdpos-audit.json` (head,
  source/dependency/olean/log SHA-256, per-declaration axiom list).
- No Arb/FLINT certificate is involved: the statements are exact identities and inequalities, so no
  precision claim is made.
