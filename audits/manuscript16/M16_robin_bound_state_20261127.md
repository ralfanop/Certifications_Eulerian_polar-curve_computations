# M16 v16.5 §14.2, Proposition 14.2: the Robin bound state `u_β` is an eigenvector of the self-adjoint `H_R`, the eigenvalue `t₀ = c − β²` is simple, `Q` projects onto its eigenspace, and `−Q` is the residue of `(H_R − t)⁻¹` — 27 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletBoundState20261127.lean` (22 audited declarations), SHA-256
`72b09bcf7b7e6956bba15d008d47cef4afd81c172cc8a08b4fc478981709bac6`. It imports `Mathlib`,
`Manuscript16.RobinDirichletPole20261125` (#604) and `Manuscript16.RobinDirichletLevelIndependence20261126`
(#632), hence the merged Robin–Dirichlet modules of #603, #605, #606, #607, #610, #611, all unchanged in
`main` = `5533364898158c486794bf101072b665ca16de97` (branch base) and not re-proved.

## Starting point

The register `audits/M16_M17_exact_head_audit_20261124.md` records for the pole of Proposition 14.2 (#604) that
`u_β = √(2β) e^{−βz}` solves `−u'' + c u = t₀ u` classically with `u'(0) = −β u(0)` and that
`(t − t₀) P_{√(c−t)} → −Q`, `Q = |u_β⟩⟨u_β|`, but "`u_β` is not called an eigenvector of an operator
realisation, nor `Q` a spectral projection", and the section "Post-merge consistency of `main` (#598, #599,
#604)" states: "That `u_β` is an eigenvector of `H_R` and `Q` its spectral projection is not claimed by any
row". Since #611 and #632, `H_R` is one self-adjoint operator on `L²(0,∞)` with `(H_R − t)⁻¹ = K_R(√(c − t))`
for every `t < t₀`. This file closes the gap between #604 and the operator `H_R`. No open PR touches
Manuscript 16 or 17 (checked 27 Nov 2026, 11:55 UTC through the REST API: the open PRs #657, #653, #633, #627,
#626, #584, #474, #394 concern Manuscripts 11–15, `SharedCore` or `SpecialImaginaryPoint`).

## Statements

`c = ‖κ‖²`, `β > 0`, `t₀ = c − β²`, `μ` Lebesgue measure on `(0,∞)`, `L2 = L²((0,∞); ℂ)`; for `a > 0`,
`K_D(a) = KDop`, `K_R(a) = KRop = KDop + robinDiff` (#605); `HD a t = t + K_D(a)⁻¹`, `HR a β t = t + K_R(a)⁻¹`
(#611, `realisation`); `v_b = vvec b` the class of `e^{−bz}`, `u_β = eigVec β = √(2β) v_β`,
`Q = eigProj β = |u_β⟩⟨u_β|` (#604).

| Declaration | Statement |
|---|---|
| `continuous_eigFun`, `memLp_eigFun`, `vvec_eq_toLp` | `e^{−βz}` is continuous and in `L²(0,∞)`; `v_β` is its class |
| `solR_eigFun` | for `0 < β < a`, `z ≥ 0`: `solR a β e^{−β·} (z) = e^{−βz}/(a² − β²)` (the right side is a bounded classical solution of `−u'' + a²u = e^{−βz}`, `u'(0) = −βu(0)`; uniqueness of #603) |
| `KRop_vvec` | **`K_R(a) v_β = (a² − β²)⁻¹ v_β`** for `0 < β < a` |
| `robinDiff_vvec` | `P_a v_β = (a² − β²)⁻¹ v_a` (`⟪v_a, v_β⟫ = 1/(a+β)`, #604) |
| `KDop_vvec` | **`K_D(a) v_β = (a² − β²)⁻¹ (v_β − v_a)`**, i.e. `∫₀^∞ G_D(z,w) e^{−βw} dw = (e^{−βz} − e^{−az})/(a² − β²)` |
| `KRop_smul_vvec` | `K_R(a)((a² − β²) c v_β) = c v_β` for every `c ∈ ℂ` |
| `HR_smul_vvec`, `HR_eigVec` | **`c v_β ∈ dom H_R` and `H_R (c v_β) = (t + a² − β²) c v_β`**; in particular `H_R u_β = (t + a² − β²) u_β` for `H_R = t + K_R(a)⁻¹` |
| `eq_zero_of_eq_smul_KDop` | `x = s K_D(a) x` with `0 ≤ s < a²` forces `x = 0` (`‖K_D(a)‖ ≤ a⁻²`, #605) |
| `HR_eigen_mem_span` | **simplicity**: `u ∈ dom H_R`, `H_R u = (t + a² − β²) u` ⇒ `u ∈ ℂ v_β` |
| `HR_eigenspace` | `ker(H_R − (t + a² − β²)) = ℂ v_β` |
| `range_eigProj_eq_eigenspace` | **`ran Q = ker(H_R − (t + a² − β²))`** |
| `eq_zero_of_resolvent` | if `R (T u − λu) = u` on `dom T`, then `T u = λu` forces `u = 0` |
| `KDopT`, `KDopT_eq`, `KRopT`, `KRopT_eq` | `K_D(a)`, `K_R(a) = K_D(a) + P_a` as total functions of the parameters, equal to `KDop`, `KRop` for `a > 0` |
| `tendsto_smul_KDopT_spectral` | `(t − t₀) K_D(√(c − t)) → 0` in operator norm as `t ↑ t₀` (`‖K_D(a)‖ ≤ a⁻² ≤ β⁻²`) |
| `tendsto_resolvent_residue` | **`(t − t₀) K_R(√(c − t)) → −Q`** in operator norm as `t ↑ t₀` (with `tendsto_residue_spectral` of #604) |
| `prop14_2_bound_state` | manuscript form below |

`prop14_2_bound_state`: fix a level `t₁ < t₀`, `a₁ = √(c − t₁)`, `H_D = HD a₁ t₁`, `H_R = HR a₁ β t₁`
(self-adjoint, #611; independent of `t₁`, #632). Then

1. `H_R` is self-adjoint, `‖u_β‖ = 1`, `u_β ∈ dom H_R` and **`H_R u_β = t₀ u_β`**;
2. `Q` is an orthogonal projection (`IsStarProjection`) with `finrank (ran Q) = 1` and
   **`x ∈ ran Q ⇔ x ∈ dom H_R ∧ H_R x = t₀ x`**: the eigenvalue `t₀` is simple and `Q` is the orthogonal
   projection onto `ker(H_R − t₀)`;
3. `H_R` has no eigenvalue `λ < t₀` and `H_D` has no eigenvalue `λ < c` (real `λ`);
4. for every `t < t₀`: `K_R(√(c − t))` is the two-sided inverse of `H_R − t` on `L²(0,∞)` and
   `K_R(√(c − t)) u_β = (t₀ − t)⁻¹ u_β`;
5. **`(t − t₀)(H_R − t)⁻¹ = (t − t₀) K_R(√(c − t)) → −Q`** in operator norm as `t ↑ t₀`.

Together with #632 (for every real `λ < t₀`, `H_R − λ` has the bounded two-sided inverse
`K_R(√(c − λ))`), item 1 shows that `t₀` is the bottom of the spectrum of `H_R` in the sense of bounded
invertibility: every `λ < t₀` is a resolvent point and `t₀` is an eigenvalue.

## Method

For `0 < β < a`, `u(z) = e^{−βz}/(a² − β²)` satisfies `u'' = a²u − e^{−βz}`, `u'(0) = −βu(0)` and
`|u| ≤ (a² − β²)⁻¹` on `[0,∞)`; the classical Robin solution `solR a β e^{−β·}` is bounded (`solR_bounded`,
#632); the uniqueness theorem `robin_solution_unique` of #603 identifies them, and `KR_toLp` (#603) with
`KRop_ae_eq` (#605) gives `K_R(a) v_β = (a² − β²)⁻¹ v_β` in `L²(0,∞)`. Since `H_R = t + K_R(a)⁻¹` with domain
`ran K_R(a)`, `v_β = K_R(a)((a² − β²) v_β) ∈ dom H_R` and `realisation_apply_K` (#611) gives
`H_R v_β = (a² − β²) v_β + t v_β`. For simplicity, put `s = a² − β²` and `T = I − s K_D(a)`; if
`H_R u = (t + s) u` then `K_R(a)(s u) = u` (`K_realisation_sub`, #611), hence
`T u = s P_a u = s (a − β)⁻¹ ⟪v_a, u⟫ v_a`, while `T v_β = s (a − β)⁻¹ (a + β)⁻¹ v_a = v_a`; so
`T(u − c₁ v_β) = 0` with `c₁ = s (a − β)⁻¹ ⟪v_a, u⟫`, and `T` is injective because
`‖s K_D(a)‖ ≤ s/a² < 1`. For the residue, `(t − t₀) K_R = (t − t₀) K_D + (t − t₀) P_a`; the first term has norm
`≤ |t − t₀| β⁻²` for `t < t₀` and tends to `0`, the second tends to `−Q` by #604. No eigenvalue below the
resolvent half-lines: if `R(T u − λu) = u` and `T u = λu`, then `u = R 0 = 0`; for `H_R` the inverse at `λ < t₀`
is `K_R(√(c − λ))` (#632), for `H_D` at `λ < c` it is `K_D(√(c − λ))` through `HD_eq_of_level` (#632).

## Published results cited (not re-proved)

- The orthogonal projection onto `ker(H − λ)` of a self-adjoint operator `H` is its spectral projection
  `E_H({λ})` (spectral theorem for unbounded self-adjoint operators; e.g. Reed–Simon, *Methods of Modern
  Mathematical Physics I*, Ch. VIII; Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, 2012,
  Ch. 5). Mathlib has no spectral theorem for unbounded operators at the pinned commit; what is proved here is
  that `Q` is the orthogonal projection onto `ker(H_R − t₀)` and that `−Q` is the norm limit of
  `(t − t₀)(H_R − t)⁻¹` as `t ↑ t₀`.

## Not claimed

- The resolvent of `H_R` at levels `t₀ < t < c` and the limit `t ↓ t₀` (the Green operators of #603–#632 are
  built for `a > β` only); that `t₀` is an isolated point of `σ(H_R)` on its right.
- The essential spectrum `[c, ∞)` of `H_D`, `H_R` and the absence of further eigenvalues in `(t₀, c)`.
- Identification of `H_D`, `H_R` with the `H²(0,∞)` realisations; essential self-adjointness on the cores of
  #610; Schatten-ideal membership; any Maxwell identification.
- Correspondence with the printed Proposition 14.2 of `16.tex` (source not in the repository).

## Verification

Local run on the pinned toolchain (`lake env lean -M16768 -o …`, Mathlib cache of the pinned commit): the 8
imported Robin–Dirichlet modules recompiled with exit 0 and no warning; the new module compiled with exit 0,
no error, no warning, no `Try this`; 22 declarations (4 wrapped axiom lists) and 296 imported reports (52 wrapped
lists), each limited to `propext`, `Classical.choice`, `Quot.sound`. The audit step of the new workflow was
replayed locally on these logs: `SUCCESS: 22 declarations ( 4 wrapped lists ) and 296 imported reports
( 52 wrapped lists ); standard axioms only`. No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or
`extern` in the new module or its local dependencies.

Certifying run: `.github/workflows/m16-robin-bound-state-20261127.yml` on the exact PR head (exact-HEAD checkout,
pinned toolchain and Mathlib asserted, compilation of the 8 imported modules and of the new module, failure on
any error, `sorryAx`, `Lean.ofReduceBool`, and on any warning in the new module, line-based axiom parser with
count checks so that names with primes and wrapped lists are included, artifacts). Not yet run when this record
was written.
