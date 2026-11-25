# M16 v16.5 §14.2 — Robin pole at `a = β`, residue and eigenprojection (Lean 4)

Date: 25 November 2026. Scope: Manuscript 16 only. No manuscript source (LaTeX) is modified;
Manuscripts 11–15 are untouched.

Analytic source: `audits/Manuscript16_v16_5_RobinResolventRankOne_20261116.md` (Proposition 14.2,
equations (147)–(149) of the author-approved `16.tex`, ZIP SHA-256
`4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e`; the printed labels still have
to be checked against the source, which was not available to the certifying run).

That note states, after the rank-one resolvent difference certified in
`lean/Manuscript16/RobinDirichletRankOne20261125.lean` (PR #603):

> The Robin resolvent has a simple pole at `a = β`, corresponding to `t = c − β²`. The normalized
> eigenfunction is `√(2β) exp(−βz)`. The pole residue in the **spectral parameter** `t` equals
> minus the eigenprojection.

Those three assertions are listed in #603 as *not claimed*; they are the obligation discharged
here. Nothing proved in #603 is re-proved: this module imports it.

## File

`lean/Manuscript16/RobinDirichletPole20261125.lean`, SHA-256
`a6e779f3d8baf86cf6dd0e1c65681618c0c1f742c9aa545ba49da891f489434c`;
38 theorems, imports `Mathlib` and `Manuscript16.RobinDirichletRankOne20261125`
(SHA-256 `78663893e197799f53ae47ef4ec670314cf8770982475d6d02746042e6dad6fc`, 64 theorems).

Notation: `μ` = Lebesgue measure on `(0,∞)`, `L2 = L²((0,∞); ℂ)`, `v_a(z) = e^{−az}` (`vvec a`,
the total extension of `expVec` of #603 by `0` for `a ≤ 0`), `P_a = (a−β)⁻¹ |v_a⟩⟨v_a|`
(`robinDiffT a β`, the total extension of `robinDiff`; `robinDiffT_eq` and `norm_robinDiffT`
identify the two for `a > 0`), `a = √(c − t)` (`aOf c t` of #603), `c = |κ|²`, `t₀ = c − β²`.

## Declarations proved

Exact geometry of the exponential family (new, two-parameter):

* `inner_expVec`, `inner_vvec`: `⟪v_a, v_b⟫ = 1/(a+b)` for `a, b > 0`.
* `norm_vvec_sub_sq`, `norm_vvec_sub`: `‖v_a − v_b‖² = (a−b)²/(2ab(a+b))`, exactly; hence
  `tendsto_vvec`: `a ↦ v_a` is right continuous at `β > 0` in `L²(0,∞)`.

Normalized eigenfunction at the pole:

* `hasDerivAt_eigFun`, `hasDerivAt_eigFun_deriv`: `u(z) = e^{−βz}` is twice differentiable with
  `u' = −β u`, `u'' = β² u` on all of `ℝ`.
* `eigFun_ode`: `−u'' + c u = (c − β²) u`, i.e. the classical eigenvalue equation at `t₀ = c − β²`.
* `hasDerivAt_eigFun_zero`: the Robin boundary condition `u'(0) = −β u(0)`.
* `eigVec`, `norm_eigVec`, `eigVec_ae`, `eigVec_ne_zero`: `u_β = √(2β) v_β` is a unit vector of
  `L²(0,∞)` whose class is the function `√(2β) e^{−βz}`.

Eigenprojection:

* `eigProj = |u_β⟩⟨u_β|` with `eigProj_isStarProjection` (self-adjoint idempotent, i.e. an
  orthogonal projection), `eigProj_isIdempotentElem`, `eigProj_isPositive`, `norm_eigProj = 1`,
  `eigProj_apply_eigVec` (`Q u_β = u_β`), `range_eigProj = ℂ ∙ v_β`, `finrank_range_eigProj = 1`.
* `rankOne_vvec_eq`: `|v_β⟩⟨v_β| = (2β)⁻¹ Q`.

Quantitative continuity of the rank-one map (used for both limits, and of independent use):

* `rankOne_self_sub`: `|x⟩⟨x| − |y⟩⟨y| = |x−y⟩⟨x| + |y⟩⟨x−y|`.
* `norm_rankOne_self_sub`: `‖|x⟩⟨x| − |y⟩⟨y|‖ ≤ ‖x−y‖ (‖x‖ + ‖y‖)`.
* `tendsto_rankOne_self`: `g → x` in `L²` implies `|g⟩⟨g| → |x⟩⟨x|` in operator norm.

Pole and residue:

* `smul_robinDiffT`: the exact simple-pole normalisation `(a − β) P_a = |v_a⟩⟨v_a|` for `β < a`.
* `tendsto_norm_robinDiffT`: `‖P_a‖ = 1/(2a(a−β)) → ∞` as `a ↓ β` (`𝓝[>] β`, `atTop`).
* `tendsto_residue_param`: `(a − β) P_a → (2β)⁻¹ Q` in operator norm as `a ↓ β`.
* `tendsto_aOf`: `t ↦ √(c−t)` maps `𝓝[<] t₀` to `𝓝[>] β`.
* `smul_robinDiffT_spectral`: the exact identity `(t − t₀) P_{√(c−t)} = −(a+β) |v_a⟩⟨v_a|` for
  every `t < t₀`.
* `tendsto_norm_robinDiffT_spectral`: `‖P_{√(c−t)}‖ → ∞` as `t ↑ t₀`.
* `tendsto_residue_spectral`: **`(t − t₀) P_{√(c−t)} → −Q` as `t ↑ t₀`** — the residue in the
  spectral parameter is minus the eigenprojection, which is the assertion of the audit note.
* `prop14_2_pole`: manuscript form with `κ ∈ EuclideanSpace ℝ (Fin 2)`, `c = ‖κ‖²`, `β > 0`,
  `t₀ = ‖κ‖² − β²`, collecting the unit eigenfunction, the eigenvalue equation, the Robin
  condition, the projection properties, the blow-up and the residue.

## Not claimed

* The self-adjoint Robin and Dirichlet realisations on `H²(0,∞)` (trace theorem, domains) and the
  identification of the integral operators `K_D`, `K_R` of #603 with their resolvents on all of
  `L²`. Consequently `u_β` is **not** asserted to be an eigenvector of an operator realisation,
  and `Q` is **not** asserted to be a spectral projection of one: the eigenvalue equation and the
  Robin condition are proved for the classical function `e^{−βz}`, and the pole and residue
  statements are proved for the rank-one family `P_a` certified in #603.
* `L²`-boundedness of `K_D`, `K_R`; Schatten-ideal (trace-class) membership; preservation of the
  essential spectrum; any Maxwell or geometric identification.
* Correspondence with the printed Proposition 14.2 of the current `16.tex` (source not available
  to this run).

## Verification

* Local, pinned toolchain `leanprover/lean4:v4.35.0-rc3`, Mathlib
  `0272bbe1c093d038d7257ab15306abd58245f9ff`: both modules compile with exit code 0 and **no**
  message (no error, no warning, no `Try this`); `#print axioms` on all 38 theorems of this
  module and all 64 theorems of the imported module reports only
  `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`, `unsafe`,
  `implemented_by`, `extern`, no `continue-on-error`, no module removed or weakened.
* Certifying run: `.github/workflows/m16-robin-dirichlet-pole-20261125.yml` — checkout of the
  exact PR head, assertion of the head SHA, of the toolchain file and of the Mathlib pin,
  compilation of the imported module and of the new module, failure on any error, warning,
  `Try this`, `sorryAx`, `Lean.ofReduceBool` or non-standard axiom, and upload of the logs and of
  `m16-rdp-audit.json` (head, source/dependency/olean/log SHA-256, per-theorem axiom list).
* No Arb/FLINT certificate is involved: every identity here is exact and symbolic, so no
  precision claim is made.
