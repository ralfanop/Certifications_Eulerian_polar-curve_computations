# M16 §14.5 `eq:hol-integral`: the operators `e^{−2t√B}` through the continuous functional calculus of `B⁻¹` — 27 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/HolonomyFunctionalCalculus20261127.lean` (30 audited declarations), SHA-256
`d924a41b70b1dbf56372f86255d330ac4f01dcc5de4a6c19bfefbf47bbf3a1f5`. It imports `Mathlib`,
`Manuscript16.HolonomyCircleResolvent20261125` (#599, merged as `b9ee66b2`) and
`Manuscript16.HolonomyCircleGenerator20261125` (#622, merged as `2cf112a7`), both unchanged in
`main` = `e8e9fb2ccc2c354188288d3c463bce1ebb3aaaa4` (branch base) and not re-proved.

## Starting point

The register `audits/M16_M17_exact_head_audit_20261124.md` (section "Post-merge consistency of `main`
(#622)") lists as still open for `eq:hol-integral`: "trace class and basis independence (cited, Simon
2005), the functional calculus `e^{−2t√B}`". In #599 the operators `evanescent a φ t` are *defined* as
the Fourier multipliers with symbol `e^{−2t√b_n}`; #622 realises `B = (D − φ)² + a²` as a self-adjoint
operator with `resolvent = B⁻¹`; no theorem connected the two through a functional calculus. This file
discharges that item in the form available at the pinned Mathlib commit (continuous functional calculus
of bounded self-adjoint operators). No open PR touches Manuscript 16 or 17 (checked 27 Nov 2026, 08:55 UTC
through the REST API: the open PRs #634, #633, #627, #626, #584, #565, #394 concern Manuscripts 11–15 and
#474 concerns `SharedCore` trace files; none touches `lean/Manuscript16`, `lean/Manuscript17`, the
Fefferman/Cassini files of `lean/EulerianCert`, `numerics/arb/m16*`, `m17*` or the M16/M17 audits).

## Statements

`S¹ = ℝ/2πℤ`, `L2Circle = L²(S¹)`, `e_n(θ) = e^{inθ}`, `b_n = circleEig a φ n = (n − φ)² + a²`,
`a > 0`, `φ` real; `R = resolvent a φ` (#599) is `B⁻¹` for `B = generator a φ` (#622); `cfc` is Mathlib's
continuous functional calculus of the self-adjoint element `R` of the C⋆-algebra `B(L²(S¹))`.

| Declaration | Statement |
|---|---|
| `instAlgRealL2Circle`, `algebraMap_real` | the real algebra structure of `B(L²(S¹))` used by Mathlib's real `cfc` (restriction of scalars from `ℂ`, `Algebra.complexToReal`), selected by a local instance; `algebraMap ℝ r = (r : ℂ) • 1` |
| `mem_spectrum_of_eigenvector`, `circleMode_ne_zero`, `eig_mem_spectrum` | an eigenvalue of a bounded operator lies in its real spectrum; **`1/b_n ∈ σ(R)` for every `n ∈ ℤ`** |
| `specPt`, `diagSymbol`, `diagSymbol_norm_le`, `diagOp`, `diagOp_mode`, `diagOp_ext`, `diagOp_norm_le`, `diagOp_isSelfAdjoint` | for `f ∈ C(σ(R), ℝ)`: the Fourier multiplier with symbol `f(1/b_n)`, `‖·‖ ≤ ‖f‖_∞`, self-adjoint, determined by its action on the modes |
| `diagHom`, `diagHom_apply`, `diagHom_continuous`, `diagHom_id` | `f ↦ diagOp f` is a **continuous star-algebra homomorphism `C(σ(R), ℝ) → B(L²(S¹))` sending the identity to `R`** |
| `cfcHom_resolvent_eq` | **`cfcHom R = diagHom`** (uniqueness of the continuous functional calculus, Mathlib `cfcHom_eq_of_continuous_of_map_id`) |
| `cfc_resolvent_mode`, `cfc_resolvent_eq_multiplier` | **for every `g : ℝ → ℝ` continuous on `σ(R)`: `cfc g R e_n = g(1/b_n) e_n`, and `cfc g R` is the Fourier multiplier with symbol `g(1/b_n)`** |
| `cfc_sqrt_resolvent_mode` | `cfc √· R e_n = b_n^{−1/2} e_n`: `(B⁻¹)^{1/2} = (√B)⁻¹` on the Fourier basis |
| `cfc_resolvent_generator` | for every `g` and every `u ∈ dom B`: `cfc g R u ∈ dom B` and **`B (cfc g R u) = cfc g R (B u)`** |
| `evGen`, `evGen_tendsto_zero`, `evGen_continuous`, `evGen_inv_eig` | `evGen t x = e^{−2t/√x}` (`x > 0`), `0` (`x ≤ 0`); continuous on `ℝ` for `t > 0`; `evGen t (1/b_n) = e^{−2t√b_n}` |
| `cfc_evGen_mode` | `cfc (evGen t) R e_n = e^{−2t√b_n} e_n` for `t > 0` |
| `evanescent_eq_cfc` | **`evanescent a φ t = cfc (evGen t) (B⁻¹)` for every `t > 0`**: the multipliers of #599 are the operators `e^{−2t√B}` given by the continuous functional calculus of `B⁻¹` |
| `integrand_eq` | the integrands of `eq:hol-integral` with the two descriptions of `e^{−2z√B}` agree for `z > 0` |
| `hol_integral_functional_calculus` | manuscript form: `B (R f) = f`, `R (B u) = u`; with `e^{−2z√B} := cfc (evGen z) (B⁻¹)`: `e^{−2z√B} e_n = e^{−2z√b_n} e_n` (`z > 0`), `e^{−2z√B} = evanescent a φ z`, **`∫₀^∞ z ∑_{n∈ℤ} ⟪e_n, e^{−2z√B} e_n⟫ dz = momentClosed a (πa) (cos 2πφ)`** and **`∑_n ⟪e_n, B⁻¹ e_n⟫ = 4 ∫₀^∞ z ∑_n ⟪e_n, e^{−2z√B} e_n⟫ dz`** |

## Method

The eigenvalue `1/b_n` of `R` (`resolvent_mode`, #599) lies in `σ(R)` because `algebraMap(1/b_n) − R`
annihilates `e_n ≠ 0` and so is not a unit. For `f ∈ C(σ(R), ℝ)` the symbol `n ↦ f(1/b_n)` is bounded by
`‖f‖_∞`, so the multiplier of #599 is defined; products, sums, constants and the identity are checked on the
Fourier modes and transported to operators by `multiplier_unique` (#599, density of trigonometric
polynomials); real symbols give self-adjoint multipliers, so `star` is preserved. Hence `diagHom` is a
continuous star-algebra homomorphism with `diagHom(id) = R`, and Mathlib's uniqueness theorem for the
continuous functional calculus (`ContinuousMap.UniqueHom ℝ`, Stone–Weierstrass) gives `cfcHom R = diagHom`.
For `t > 0` the function `evGen t` is continuous on `ℝ` (`e^{−2t/√x} → 0` as `x ↓ 0`) and takes the value
`e^{−2t√b_n}` at `1/b_n`, so `cfc (evGen t) R` and `evanescent a φ t` agree on every mode and are equal.
Commutation with `B`: `cfc g R` commutes with `R` (Mathlib `Commute.cfc`), and `u = R (B u)` for
`u ∈ dom B` (#622), so `cfc g R u = R (cfc g R (B u)) ∈ ran R = dom B`.

The real algebra structure of `B(L²(S¹))` used by Mathlib's real functional calculus is the restriction of
scalars from `ℂ`. The `ℝ`-module structure of `Lp` gives a second, propositionally equal, instance that
type-class search finds first; the file selects the restriction of scalars by a local instance
(`instAlgRealL2Circle`), so `σ(R)` is the usual real spectrum of `R` and `cfc` is Mathlib's.

## Published results cited, not re-proved

- Continuous functional calculus of self-adjoint elements of a C⋆-algebra and its uniqueness
  (`cfcHom_eq_of_continuous_of_map_id`, Stone–Weierstrass): Mathlib at the pinned commit.
- For a self-adjoint operator `B ≥ a² > 0` with bounded inverse, the operator `h(B)` of the spectral
  theorem equals `(h ∘ ι)(B⁻¹)`, `ι(x) = 1/x` (classical spectral theory of unbounded self-adjoint
  operators). Mathlib has no functional calculus of unbounded operators at the pinned commit, so
  `e^{−2t√B}` is *defined* here as `cfc (evGen t) (B⁻¹)`; the identity with the spectral-theorem
  definition is a published result cited, not formalised.

## Not claimed

- A functional calculus of the unbounded operator `B` itself; strong continuity of `t ↦ e^{−2t√B}` and the
  identification of its generator with `−2√B`; `e^{−2t√B}` for `t = 0` through `evGen` (for `t = 0` the
  multiplier is the identity, `evanescent_zero` of #599, and `cfc 1 R = 1`).
- Trace-class membership and basis independence of the diagonal sums (Lidskii; Simon 2005), as before.
- Any Maxwell or geometric statement; the correspondence with the printed display of `eq:hol-integral` in
  `16.tex` (source not in the repository).

## Verification

- Local, pinned toolchain (Mathlib at `0272bbe1`, cache from `lake exe cache get`): the 22 imported
  repository modules (`SharedCore.FredholmCompactParametrix`, `SharedCore.FredholmAtkinson`,
  `V165TypedGraphSchur`, `V165GraphNeumann`, `V166CompactTransfer`, `DiracMaxwellObstructionIndex20261124`,
  `DiracMaxwellGraphSpace20261124`, `V166L2SpectralInverse`, `V166SpectralCutoffs`,
  `DiracMaxwellCoefficientModel20261124`, `V166HolonomyPair`, `ReactiveHolonomyV166`,
  `HolonomyEulerProduct20261124`, `HolonomyMomentSeries20261124`, `HolonomyCircleResolvent20261125`, the six
  Robin–Dirichlet modules of #603–#611 and `HolonomyCircleGenerator20261125`) and the new module compile with
  exit 0; the new module produces no error, warning or `Try this`; its 30 declarations depend only on
  `propext`, `Classical.choice`, `Quot.sound` (22 of the 30 lists wrap over several lines and were parsed as
  such); the 434 axiom reports of the imported modules (167 wrapped) contain only these three. The audit step
  of the new workflow was replayed locally on these logs: `SUCCESS: 30 declarations ( 22 wrapped lists ) and
  434 imported reports ( 167 wrapped lists ); standard axioms only`.
- Certifying run: `.github/workflows/m16-hol-functional-calculus-20261127.yml` (exact-HEAD checkout and SHA
  assertion, pinned toolchain and Mathlib asserted, compilation of the 22 imported modules and of the new
  module, failure on any error, `sorryAx`, `Lean.ofReduceBool`, on any warning or `Try this` in the new
  module and on any non-standard axiom; line-based parser of the axiom reports, so that names with primes and
  wrapped lists are included, with a count check against the report lines; artifact with per-declaration
  axiom lists).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
