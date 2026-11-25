# M16 v16.5 §14.2, Proposition 14.2: Robin–Dirichlet resolvent difference of rank one — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletRankOne20261125.lean` (64 audited theorems; imports Mathlib only).

## Starting point

`audits/Manuscript16_v16_5_RobinResolventRankOne_20261116.md` records Proposition 14.2 (equations
(147)–(149) of the v16.5 source, labels to be verified): for `c = |κ|²`, `β > 0`, real `t < c − β²`,
`a = √(c − t) > β`, with Green kernels

- `G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)`,
- `G_R(z,w) = (e^{−a|z−w|} + ((a+β)/(a−β)) e^{−a(z+w)})/(2a)`,

`(H_R − t)⁻¹ − (H_D − t)⁻¹ = (a−β)⁻¹ |v_a⟩⟨v_a|`, `v_a(z) = e^{−az}`, positive, rank one, trace
`1/(2a(a−β))`. Its Lean obligations were all open. In `main` the only Robin statement is the scalar
`te_robin_coefficient` of `ReactiveHolonomyV166.lean` (a different identity, `thm:te-robin`). No open
PR treats §14.2 (checked 25 Nov 2026, 04:00 UTC: the open M16 PRs #597–#602 concern §14.1 and §14.5;
the other open PRs concern M11–M14 and `SpecialImaginaryPoint`, #474).

## What is proved

`μ` is Lebesgue measure on `(0, ∞)`, `L2 = L²((0,∞); ℂ)` (Mathlib `Lp ℂ 2 μ`).

| Declaration | Statement |
|---|---|
| `scalar_identity`, `greenR_sub_greenD` | `((a+β)/(a−β) + 1)/(2a) = 1/(a−β)`; `G_R − G_D = e^{−az} e^{−aw}/(a−β)` (free term cancels) |
| `greenD_symm`, `greenR_symm`, `greenD_zero_left` | symmetry of both kernels; `G_D(0,w) = 0` for `w ≥ 0` |
| `greenR_robin_condition` | `∂_z G_R(0,w) = −β G_R(0,w)` for every `w > 0` (`HasDerivAt`) |
| `memLp_exp`, `inner_expVec_self`, `norm_expVec_sq` | `v_a ∈ L²(0,∞)`, `⟪v_a, v_a⟫ = ‖v_a‖² = 1/(2a)` |
| `robinDiff`, `robinDiff_apply` | `P_a = (a−β)⁻¹ |v_a⟩⟨v_a|` (Mathlib `rankOne`), `P_a f = (a−β)⁻¹ ⟪v_a, f⟫ v_a` |
| `robinDiff_isPositive` | `P_a` positive (Mathlib `ContinuousLinearMap.IsPositive`) for `β < a` |
| `range_robinDiff`, `finrank_range_robinDiff` | range of `P_a` is `ℂ v_a`; **rank one** |
| `norm_robinDiff` | **`‖P_a‖ = 1/(2a(a−β))`** |
| `robinDiff_diagonal_hasSum` | for **every** Hilbert basis `(e_i)` of `L²(0,∞)`: `∑ ⟪e_i, P_a e_i⟫` converges to **`1/(2a(a−β))`** |
| `memLp_greenD`, `memLp_greenR`, `kD`, `kR` | `G_D(z,·), G_R(z,·) ∈ L²(0,∞)` for every real `z` (bound `C_z e^{−aw}`) |
| `KD_eq_integral`, `KR_eq_integral` | `(K_D f)(z) = ∫₀^∞ G_D(z,w) f(w) dw`, `(K_R f)(z) = ∫₀^∞ G_R(z,w) f(w) dw`, every `f ∈ L²`, every `z` |
| `kR_sub_kD`, `KR_sub_KD` | `G_R(z,·) − G_D(z,·) = (a−β)⁻¹ e^{−az} v_a` in `L²`; `(K_R f)(z) − (K_D f)(z) = (a−β)⁻¹ e^{−az} ⟪v_a, f⟫` |
| `robinDiff_ae_eq` | **`P_a f = K_R f − K_D f`** in `L²(0,∞)`, every `f ∈ L²` |
| `kD_zero`, `KD_zero_left` | `G_D(0,·) = 0` in `L²`; `(K_D f)(0) = 0` |
| `solD`, `solR`, `hasDerivAt_solD`, `hasDerivAt_solD'`, `hasDerivAt_solR`, `hasDerivAt_solR'` | variation-of-parameters solutions, twice differentiable on `ℝ`, `−u'' + a² u = f`, for continuous `f` |
| `solD_zero`, `solR_robin` | `u_D(0) = 0`; `u_R'(0) = −β u_R(0)` |
| `integral_greenD_mul`, `integral_greenR_mul` | `∫₀^∞ G_D(z,w) f(w) dw = u_D(z)`, `∫₀^∞ G_R(z,w) f(w) dw = u_R(z)` for `z ≥ 0`, continuous `f` with `e^{−aw} f ∈ L¹(0,∞)` |
| `KD_toLp`, `KR_toLp` | for continuous `f ∈ L²(0,∞)` (with `e^{−aw} f ∈ L¹`): `K_D f = u_D`, `K_R f = u_R` on `[0,∞)` |
| `bounded_solution_eq`, `dirichlet_uniqueness`, `robin_uniqueness` | a bounded classical solution of `u'' = a² u` on `[0,∞)` (one-sided derivatives at `0`) is `u(0) e^{−az}`; it vanishes under the Dirichlet condition, or under the Robin condition when `β < a` |
| `dirichlet_solution_unique`, `robin_solution_unique` | `u_D` (resp. `u_R`) is the unique bounded classical solution of the Dirichlet (resp. Robin) problem, given that `u_D` (resp. `u_R`) is bounded |
| `aOf`, `lt_aOf`, `aOf_pos`, `aOf_sq`, `prop14_2` | manuscript form: `κ ∈ EuclideanSpace ℝ (Fin 2)`, `β > 0`, `t < ‖κ‖² − β²`, `a = √(‖κ‖² − t) > β`, `a² = ‖κ‖² − t`; `P_a` positive, rank one, `‖P_a‖ = 1/(2a(a−β))`, `P_a = K_R − K_D` on `L²`, diagonal sum `1/(2a(a−β))` on every Hilbert basis |

Obligations of the 16 Nov 2026 note discharged: the scalar identity; the boundary conditions of the
kernels (Dirichlet value, Robin derivative); the rank-one operator identity `K_R − K_D = P_a` on
`L²(0,∞)` for the integral operators defined by the printed kernels; the trace value `1/(2a(a−β))`
as a basis-independent diagonal sum; the classical boundary-value problems solved by the kernels and
uniqueness among bounded classical solutions.

## Not claimed

- The self-adjoint Robin and Dirichlet realisations of `−d²/dz² + c` on the half-line Sobolev space
  `H²(0,∞)` (trace theorem, operator domains) and the identification of `K_D`, `K_R` with
  `(H_D − t)⁻¹`, `(H_R − t)⁻¹` on all of `L²(0,∞)`. Only classical solutions for continuous data are
  treated (Part D) and uniqueness is among bounded classical solutions (Part E).
- Boundedness of `K_D`, `K_R` as operators on `L²(0,∞)` (they are defined pointwise through
  `⟪G(z,·), f⟫`); only their difference is identified with the bounded operator `P_a`.
- Trace-class membership in the Schatten-ideal sense (no Schatten classes in Mathlib at the pinned
  commit): for this rank-one operator the diagonal sum is proved on every Hilbert basis.
- The simple pole at `a = β` (`t = c − β²`), its residue and the eigenprojection onto
  `√(2β) e^{−βz}`; preservation of the essential spectrum.
- Any Maxwell identification or geometric statement.
- The match of the labels, equation numbers and parameter names with the printed Proposition 14.2 of
  the current `16.tex` still has to be checked against the source, which was not available to this
  run; the statement used is the one recorded in the 16 Nov 2026 note.

## Verification

Local (pinned toolchain `v4.35.0-rc3`, Mathlib `0272bbe1`): exit 0, no message from the file
(no error, no warning, no `Try this`); 64/64 theorems depend only on `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `extern` in the source.
Certifying run: `.github/workflows/m16-robin-dirichlet-rank-one-20261125.yml` (exact-HEAD checkout,
pinned toolchain and Mathlib, failure on any error, warning, `Try this` or non-standard axiom,
`#print axioms` audit of 64/64 theorems, source/olean/log SHA-256 and artifacts).

## Numerics

All identities are exact and symbolic; no FLINT/Arb computation is involved and no numerical
precision is claimed.
