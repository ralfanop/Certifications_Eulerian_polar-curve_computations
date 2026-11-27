# M16 v16.5 §14.2, Proposition 14.2: the self-adjoint operators `H_D`, `H_R` do not depend on the level `t`; first resolvent identity of the Dirichlet and Robin Green operators — 26 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletLevelIndependence20261126.lean` (39 audited declarations), SHA-256
`b8733c84cca968abf409105ba20de7d29bb316858f2f684b75ef9f8f81511621`. It imports `Mathlib` and
`Manuscript16.RobinDirichletRealisation20261125` (#611, merged as `be053cf5`), hence the merged modules of
#603, #605, #606, #607, #610, all unchanged in `main` = `e63d3fac` (branch base) and not re-proved.

## Starting point

The register `audits/M16_M17_exact_head_audit_20261124.md` (row "M16 v16.5 Proposition 14.2 (§14.2),
self-adjoint operators `H_D = t + K_D⁻¹`, `H_R = t + K_R⁻¹`", #611) lists as not claimed "identification with
the `H²(0,∞)` realisations, essential self-adjointness on the cores, independence of `t`", and the section
"Post-merge consistency of `main` (#596 … #611)" lists under "Still open for Proposition 14.2": identification
of `H_D`, `H_R` with the `H²(0,∞)` realisations, essential self-adjointness on the cores, independence of `t`,
essential spectrum, Schatten-ideal membership. In #611 each operator is built from the Green operator at one
fixed level `t`, so the printed statement `(H_R − t)⁻¹ − (H_D − t)⁻¹ = (a − β)⁻¹ |v_a⟩⟨v_a|` for all
`t < c − β²` was certified only for a family of operators that might depend on `t`. This file discharges the
item "independence of `t`". No open PR touches Manuscript 16 or 17 (checked 26 Nov 2026, 13:21 UTC through
the REST API: the open PRs #631, #628, #627, #626, #616, #584, #582, #565, #563, #474, #394 concern Manuscripts
11–15, `SharedCore` or `SpecialImaginaryPoint`; none touches `lean/Manuscript16`, `lean/Manuscript17`,
`lean/EulerianCert` Fefferman/Cassini files, `numerics/arb/m16*`, `m17*` or the M16/M17 audits).

## Statements

`c = ‖κ‖²`, `β > 0`, `μ` Lebesgue measure on `(0,∞)`, `L2 = L²((0,∞); ℂ)`; for `a > 0`, `K_D(a) = KDop`,
`K_R(a) = KRop = KDop + robinDiff` (#605) are the integral operators of the printed kernels
`G_D(z,w) = (e^{−a|z−w|} − e^{−a(z+w)})/(2a)` and `G_R(z,w) = (e^{−a|z−w|} + ((a+β)/(a−β)) e^{−a(z+w)})/(2a)`;
`HD a t = t + K_D(a)⁻¹`, `HR a β t = t + K_R(a)⁻¹` are the Mathlib `LinearPMap`s of #611 (`realisation`);
`solD`, `solR` are the variation-of-parameters solutions of #603.

| Declaration | Statement |
|---|---|
| `graphSub_eq_of_resolvent_identity`, `realisation_eq_of_resolvent_identity` | if `K₁ − K₂ = (t₁ − t₂) K₂K₁ = (t₁ − t₂) K₁K₂`, the graphs `{(K₁f, f + t₁K₁f)}`, `{(K₂g, g + t₂K₂g)}` coincide, hence **`t₁ + K₁⁻¹ = t₂ + K₂⁻¹`** as `LinearPMap`s |
| `resolvent_of_eq` | if `t + K⁻¹ = H`, then `(H − t) K f = f` for every `f` and `K (H − t) u = u` on `dom H` |
| `enorm_greenD_le_freeK`, `freeK_le`, `lintegral_greenD_sq_le`, `kerBound`, `norm_kD_le` | for `z ≥ 0`: `∫₀^∞ |G_D(z,w)|² dw ≤ a⁻²(2a)⁻¹`, so `‖G_D(z,·)‖_{L²(0,∞)} ≤ C_a` uniformly in `z ≥ 0` |
| `norm_KD_le`, `norm_KR_le` | `|(K_D f)(z)| ≤ C_a ‖f‖`, `|(K_R f)(z)| ≤ (C_a + (a−β)⁻¹‖v_a‖) ‖f‖` for every `f ∈ L²(0,∞)`, `z ≥ 0` |
| `memLp_real_of_complex`, `integrableOn_exp_mul` | `f ∈ L²(0,∞)` ⇒ `e^{−aw} f(w)` integrable on `(0,∞)` (Hölder) |
| `shiftD`, `shiftR`, `continuous_*`, `memLp_*`, `solD_bounded`, `solR_bounded` | for continuous real `g ∈ L²(0,∞)`: `u_b = solD b g`, `solR b β g` are continuous, in `L²(0,∞)` (they are `K(b) g` on `[0,∞)`) and bounded on `[0,∞)`; `g + (a² − b²) u_b` is continuous and in `L²(0,∞)` |
| `solD_level_shift`, `solR_level_shift` | **`solD b g = solD a (g + (a² − b²) solD b g)` and `solR b β g = solR a β (g + (a² − b²) solR b β g)` on `[0,∞)`** (`a, b > 0`; `β < a`, `β < b` for Robin), by the uniqueness of bounded classical solutions of #603 |
| `KDop_level_shift_toLp`, `KRop_level_shift_toLp` | `K(b) g = K(a) g + (a² − b²) K(a) K(b) g` for continuous real `g ∈ L²(0,∞)` |
| `eq_zero_of_toLp_real` | a bounded operator on `L²(0,∞)` vanishing on the continuous real functions of `L²(0,∞)` is zero (density of bounded continuous functions, Mathlib) |
| `KDop_level_shift`, `KRop_level_shift` | **`K_D(b) = K_D(a) + (a² − b²) K_D(a)K_D(b)`, `K_R(b) = K_R(a) + (a² − b²) K_R(a)K_R(b)`** on all of `L²(0,∞)` |
| `KDop_resolvent_identity`, `KRop_resolvent_identity` | **first resolvent identity** `K(a) − K(b) = (b² − a²) K(a) K(b)` for both kernels |
| `KDop_comm`, `KRop_comm` | `K(a) K(b) = K(b) K(a)` for both kernels |
| `HD_eq_of_level`, `HR_eq_of_level` | **`t + K_D(a)⁻¹ = s + K_D(b)⁻¹` and `t + K_R(a)⁻¹ = s + K_R(b)⁻¹` whenever `t + a² = s + b²`** (`a, b > 0`; `β < a`, `β < b` for Robin) |
| `level_sum` | `t + (√(c − t))² = c` for `t < c − β²` |
| `prop14_2_level_independence` | manuscript form: fix `t₀ < c − β²`, `a₀ = √(c − t₀)`, `H_D = HD a₀ t₀`, `H_R = HR a₀ β t₀` (self-adjoint, #611). For **every** `t < c − β²`, `a = √(c − t)`: `HD a t = H_D`, `HR a β t = H_R`; `(H_D − t) K_D(a) f = f`, `K_D(a)(H_D − t) u = u`, `(H_R − t) K_R(a) f = f`, `K_R(a)(H_R − t) u = u`; `K(a) − K(a₀) = (t − t₀) K(a) K(a₀)` for both kernels; `K_R(a) − K_D(a) = (a − β)⁻¹ |v_a⟩⟨v_a|` (#605). Hence `(H_R − t)⁻¹ − (H_D − t)⁻¹ = (a − β)⁻¹ |v_a⟩⟨v_a|` for one fixed pair of self-adjoint operators and every level `t < c − β²` |

## Method

For continuous real `g ∈ L²(0,∞)` the classical Dirichlet solution `u_b = solD b g` at level `b` (#603) is
`C²`, vanishes at `0`, and is bounded on `[0,∞)` because `|u_b(z)| = |⟪G_D(z,·), g⟫| ≤ C_b ‖g‖` (Cauchy–Schwarz
with the uniform kernel bound, obtained from the free-kernel row bound `row_freeK` of #605 and
`0 ≤ G_D ≤ e^{−a|z−w|}/(2a)`). Since `−u_b'' + a² u_b = g + (a² − b²) u_b`, the uniqueness of bounded classical
solutions (#603, `dirichlet_solution_unique`) identifies `u_b` with the classical solution at level `a` for the
datum `g + (a² − b²) u_b`; with `KD_toLp` of #603 and `KDop_ae_eq` of #605 this is the identity
`K_D(b) g = K_D(a) g + (a² − b²) K_D(a) K_D(b) g` in `L²(0,∞)`. The same argument with `solR`,
`robin_solution_unique` (`β < a`) and `KRop_ae_eq` gives the Robin identity. Both sides are bounded operators;
splitting a continuous complex function into real and imaginary parts and using the density of bounded
continuous functions in `L²(0,∞)` (Mathlib `MemLp.exists_boundedContinuous_eLpNorm_sub_le`; the half-line
Lebesgue measure is locally finite on a second-countable metric space, hence weakly regular) extends the
identity to all of `L²(0,∞)`. Exchanging `a` and `b` gives both orderings of the product, and the graph
computation of Part A turns the first resolvent identity into the equality of the operators `t + K(a)⁻¹`.

## Published results cited, not re-proved

- Density of bounded continuous functions in `L^p` (`p < ∞`) of a weakly regular measure, and the weak
  regularity of locally finite measures on second-countable metric spaces: Mathlib at the pinned commit.
- Hölder's inequality: Mathlib `MemLp.integrable_mul`.

## Not claimed

- That `H_D`, `H_R` coincide with the realisations of `−d²/dz² + c` on the Sobolev domains
  `{u ∈ H²(0,∞) : u(0) = 0}` and `{u ∈ H²(0,∞) : u'(0) = −β u(0)}` (no trace theorem, no half-line Sobolev
  space is used).
- Essential self-adjointness on the cores of #610.
- The spectrum or essential spectrum of `H_D`, `H_R`; Schatten-ideal membership; any Maxwell or geometric
  identification.
- The correspondence of the symbols with the printed statement of Proposition 14.2 of `16.tex` was not re-read
  in the source, which is not in the repository.

## Verification

- Local, pinned toolchain (Mathlib at `0272bbe1`, cache from `lake exe cache get`): the 6 imported repository
  modules (`RobinDirichletRankOne20261125`, `RobinDirichletL2Bounded20261125`, `RobinDirichletPositive20261125`,
  `RobinDirichletInjective20261125`, `RobinDirichletWeakResolvent20261125`, `RobinDirichletRealisation20261125`)
  and the new module compile with exit 0; the new module produces no error, warning or `Try this`; its 39
  declarations depend only on `propext`, `Classical.choice`, `Quot.sound` (21 of the 39 lists wrap over several
  lines and were parsed as such); the 219 axiom reports of the imported modules (30 wrapped) contain only these
  three. The audit step of the new workflow was replayed locally on these logs: `SUCCESS: 39 declarations
  ( 21 wrapped lists ) and 219 imported reports ( 30 wrapped lists ); standard axioms only`.
- Certifying run: `.github/workflows/m16-robin-dirichlet-level-independence-20261126.yml` (exact-HEAD checkout
  and SHA assertion, pinned toolchain and Mathlib asserted, compilation of the 6 imported modules and of the new
  module, failure on any error, warning, `Try this`, `sorryAx`, `Lean.ofReduceBool` or non-standard axiom,
  count check of the imported report lines so that names with primes are included, artifact with
  per-declaration axiom lists).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
