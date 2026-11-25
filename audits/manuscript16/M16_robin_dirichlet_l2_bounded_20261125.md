# M16 v16.5 §14.2, Proposition 14.2: Dirichlet and Robin Green operators bounded on L²(0,∞) — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletL2Bounded20261125.lean` (29 audited declarations), SHA-256
`303e9028ae0b34a14e0c02dcd44db48fa4fa5bf4578aa9e8f6b05318db479e4a`. It imports `Mathlib` and
`Manuscript16.RobinDirichletRankOne20261125` (PR #603, head `0a0022bffded18c25781fec7fa94fa1c8e07d04a`,
source SHA-256 `78663893e197799f53ae47ef4ec670314cf8770982475d6d02746042e6dad6fc`), on which this
branch is stacked. Nothing of #603 or #604 is re-proved.

## Starting point

#603 defines, for `a > 0`, `f ∈ L² = L²((0,∞); ℂ)` and every `z`, the functions
`(K_D f)(z) = ∫₀^∞ G_D(z,w) f(w) dw` and `(K_R f)(z) = ∫₀^∞ G_R(z,w) f(w) dw` (`KD`, `KR`), with
`G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)`, `G_R(z,w) = (e^{−a|z−w|} + ((a+β)/(a−β)) e^{−a(z+w)})/(2a)`,
and proves `K_R f − K_D f = P_a f` a.e., `P_a = (a−β)⁻¹ |v_a⟩⟨v_a|`. Both #603 and #604 list as
**not claimed** the `L²`-boundedness of `K_D`, `K_R`: it was not known that `K_D f`, `K_R f` lie in
`L²(0,∞)`, so `K_D`, `K_R` were not operators on `L²`. That is the obligation discharged here.
No open PR treats it (checked 25 Nov 2026, 06:05 UTC: #597–#602 concern §14.1 and §14.5, #603 and
#604 state it as not claimed, #474 concerns `SpecialImaginaryPoint`/M14, the others M11–M14).

The first obligation of the run brief, `thm:dirac-maxwell-obstruction-164` (i)–(ii), is closed in
`main` by #576, #585 and #588 (see the register) and was not re-proved.

## Statements

Part A — Schur test (general, `ℝ≥0∞`-valued):

- `lintegral_mul_sq_le`: `(∫ k h)² ≤ (∫ k)(∫ k h²)` for `k, h ≥ 0` (weighted Cauchy–Schwarz, from
  Mathlib's Hölder inequality `ENNReal.lintegral_mul_norm_pow_le` with exponents `1/2, 1/2`).
- `schur_lintegral`: for a jointly measurable kernel `k ≥ 0` with row and column integrals `≤ M < ∞`
  and measurable `h ≥ 0`, `∫ (∫ k(z,w) h(w) dw)² dz ≤ M² ∫ h²` (Tonelli: `lintegral_lintegral_swap`).

Part B — free kernel:

- `integral_exp_neg_abs`: `∫_ℝ e^{−a|x|} dx = 2/a`; `integrable_exp_neg_abs`.
- `lintegral_freeK_real`: `∫_ℝ e^{−a|z−w|}/(2a) dw = 1/a²` (translation invariance of Lebesgue
  measure); `row_freeK`, `col_freeK`: on `(0,∞)` the row and column integrals are `≤ 1/a²`.
- `greenD_nonneg`, `greenD_le`, `enorm_greenD_le`: `0 ≤ G_D(z,w) ≤ e^{−a|z−w|}/(2a)` for `z, w ≥ 0`.

Part C — Dirichlet operator:

- `aestronglyMeasurable_KD`, `lintegral_KD_sq_le`, `eLpNorm_KD_le`: **`‖K_D f‖₂ ≤ a⁻² ‖f‖₂` for every
  `f ∈ L²(0,∞)`**; `memLp_KD`: `K_D f ∈ L²(0,∞)`.
- `KDop : L² →L[ℂ] L²` (`LinearMap.mkContinuous`), `KDop_ae_eq` (`KDop f = K_D f` a.e.),
  **`norm_KDop_le` (`‖K_D‖ ≤ a⁻²`)**, `KDop_unique` (the only bounded operator acting by the kernel
  `G_D`), with `KD_add`, `KD_smul`, `norm_toLp_KD_le`, `KDop_apply`.

Part D — Robin operator:

- `KRop = KDop + P_a`; `KRop_ae_eq` (`KRop f = K_R f` a.e. for every `f ∈ L²(0,∞)`), `memLp_KR`,
  **`norm_KRop_le` (`‖K_R‖ ≤ a⁻² + 1/(2a(a−β))`)**, `KRop_unique`, and **`KRop_sub_KDop`
  (`K_R − K_D = P_a` as operators on all of `L²(0,∞)`)**.

Manuscript form: `prop14_2_bounded` (`κ ∈ EuclideanSpace ℝ (Fin 2)`, `c = ‖κ‖²`, `β > 0`,
`t < c − β²`, `a = √(c − t)`): the two a.e. identities, `‖K_D‖ ≤ 1/(c − t)`,
`‖K_R‖ ≤ 1/(c − t) + 1/(2a(a−β))`, `K_R − K_D = P_a`.

## Not claimed

- The self-adjoint Dirichlet and Robin realisations `H_D`, `H_R` on `H²(0,∞)` (trace theorem,
  domains) and the identification `KDop = (H_D − t)⁻¹`, `KRop = (H_R − t)⁻¹`. Consequently the bound
  `‖K_D‖ ≤ a⁻²` is **not** called a resolvent estimate, and its sharpness is not claimed.
- Self-adjointness or positivity of `KDop`, `KRop` (the kernels are real and symmetric; the Fubini
  argument is the next step).
- Schatten-ideal membership; the essential spectrum; any Maxwell or geometric identification.
- Correspondence with the printed Proposition 14.2 of the current `16.tex` (source not available to
  this run).

## Verification

- Local, pinned toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib
  `0272bbe1c093d038d7257ab15306abd58245f9ff`: the imported module and the new module compile with exit
  code 0 and **no** message (no error, no warning, no `Try this`); `#print axioms` on all 29
  declarations of the new module and on all 64 of the imported module reports only `propext`,
  `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`,
  `extern`; no `continue-on-error`; no module removed or weakened.
- Certifying run: `.github/workflows/m16-robin-dirichlet-l2-bounded-20261125.yml` — checkout of the
  exact PR head, assertion of the head SHA, of the toolchain file and of the Mathlib pin, compilation
  of the imported and of the new module, failure on any error, warning, `Try this`, `sorryAx`,
  `Lean.ofReduceBool` or non-standard axiom, upload of the logs and of `m16-rdl2-audit.json` (head,
  source/dependency/olean/log SHA-256, per-declaration axiom list).
- No Arb/FLINT certificate is involved: the statements are exact inequalities and identities, so no
  precision claim is made.
