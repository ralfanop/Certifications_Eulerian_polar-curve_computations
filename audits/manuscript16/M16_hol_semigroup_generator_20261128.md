# M16 §14.5 `eq:hol-integral`: strong continuity of `t ↦ e^{−2t√B}` and its generator `−2√B` — 28 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/HolonomySemigroupGenerator20261128.lean` (53 audited declarations), SHA-256
`a0f813ff76e3b3b807654a205685e0e6d4f0edd925dfdba8d5e9084e23af2f4d`. It imports `Mathlib` and
`Manuscript16.HolonomyFunctionalCalculus20261127` (#643, merged as `660896cf`), hence #599 (`b9ee66b2`),
#622 (`2cf112a7`) and #611 (`be053cf5`); all are unchanged in `main` =
`2b55566561841a0ac34054c2dfadbc72c2188c7a` (branch base, merge of #715) and none is re-proved.

## Starting point

The register `audits/M16_M17_exact_head_audit_20261124.md` (section "Post-merge consistency of `main`
(#643, #645)") lists as still open for `eq:hol-integral` "strong continuity and generator of
`t ↦ e^{−2t√B}`"; the module docstring of #643 lists as not claimed "strong continuity of `t ↦ e^{−2t√B}`
and the identification of its generator with `−2√B`". Both are obligations about the specific operators
`e^{−2t√B}` of the manuscript; the other items of that list (functional calculus of the unbounded `B`,
trace class and basis independence) are published results cited and are not touched here. No open PR touches
Manuscript 16 or 17 (checked 28 Nov 2026, 06:55 UTC through the REST API: the open PRs #712, #703, #657
(Manuscript 12), #695, #679, #677, #676 (Manuscript 15), #653, #394 (Manuscript 11), #584 and #474
(Manuscript 14, `SharedCore` trace files) change no file of `lean/Manuscript16`, `lean/Manuscript17`, the
M16 Krein/S³ files, the Fefferman/Cassini files of `lean/EulerianCert`, `numerics/arb/m16*`, `m17*` or the
M16/M17 audits).

## Statements

`S¹ = ℝ/2πℤ`, `L2Circle = L²(S¹)`, `e_n(θ) = e^{inθ}`, `û_n = ⟪e_n, u⟫`, `b_n = circleEig a φ n =
(n − φ)² + a²`, `a > 0`, `φ` real; `T(t) = evanescent a φ t` (`t ≥ 0`), the Fourier multiplier with symbol
`e^{−2t√b_n}` (#599), equal to `cfc (evGen t) (B⁻¹)` for `t > 0` (#643); `B = generator a φ` (#622).

| Declaration | Statement |
|---|---|
| `repr_multiplier`, `summable_sq_repr`, `norm_sq_eq_tsum` | Fourier coefficients of a multiplier; Parseval `‖v‖² = ∑_{n∈ℤ} |v̂_n|²` |
| `tendsto_tsum_mul_sq`, `tendsto_of_norm_sq` | dominated convergence for `∑_n |c_t(n) x_n|²` with `|c_t(n)|² ≤ w_n`, `∑ w_n |x_n|² < ∞` (Mathlib `tendsto_tsum_of_dominated_convergence`); convergence in `L²(S¹)` from the squared norms |
| `repr_evanescent`, `evanescentSymbol_continuous`, `evanescentSymbol_zero`, `exp_mem_Icc`, `evanescentSymbol_sub_norm_le`, `norm_sq_evanescent_sub` | `(T(t)u)^_n = e^{−2t√b_n} û_n`; the symbol is continuous in `t`, equal to `1` at `t = 0`, in `(0, 1]`; `‖T(s)u − T(t)u‖² = ∑_n |e^{−2s√b_n} − e^{−2t√b_n}|² |û_n|²` |
| `evanescent_norm_le` | `‖T(t)‖ ≤ 1` |
| `evanescent_continuous`, `evanescent_tendsto_zero` | **strong continuity: `t ↦ T(t)u` is continuous on `[0, ∞)` for every `u ∈ L²(S¹)`**; `T(t)u → u` as `t → 0` |
| `evanescent_sub_id_mode`, `norm_evanescent_sub_id_le`, `tendsto_sqrt_circleEig_atTop`, `norm_evanescent_sub_id`, `evanescent_not_tendsto_norm` | `T(t) − I` is the multiplier `e^{−2t√b_n} − 1`; **`‖T(t) − I‖ = 1` for every `t > 0`**; `T` is not continuous in operator norm at `0` |
| `sqrt_circleEig_pos`, `le_sqrt_circleEig`, `invSqrtSymbol`, `invSqrtSymbol_norm_le` | `a ≤ √b_n`; the symbol `b_n^{−1/2}`, bounded by `1/a` |
| `invSqrt`, `invSqrt_eq_multiplier`, `repr_invSqrt`, `invSqrt_isSelfAdjoint`, `invSqrt_injective` | `invSqrt := cfc √· (B⁻¹)` (Mathlib continuous functional calculus, same real algebra structure as #643) **is the multiplier with symbol `b_n^{−1/2}`**; bounded, self-adjoint, injective |
| `sqrtGen`, `sqrtGen_isSelfAdjoint`, `mem_sqrtGen_domain`, `invSqrt_mem_domain`, `sqrtGen_invSqrt`, `invSqrt_sqrtGen`, `repr_sqrtGen` | **`√B := (cfc √· (B⁻¹))⁻¹`** (merged `realisation` of #611, `t = 0`) **is self-adjoint**; `√B (invSqrt f) = f`, `invSqrt (√B u) = u`; `(√B u)^_n = √b_n û_n` |
| `mem_sqrtGen_domain_iff`, `H1Circle`, `sqrtGen_domain_eq` | `u ∈ dom √B ⇔ ∑ b_n |û_n|² < ∞`; **`dom √B = H¹(S¹)`** in Fourier form `∑_{n∈ℤ} (1 + n²) |û_n|² < ∞` |
| `inner_sqrtGen_re` | **`Re ⟪u, √B u⟫ ≥ a ‖u‖²`** for `u ∈ dom √B` |
| `mem_generator_domain_iff_summable`, `generator_domain_le`, `sqrtGen_sq`, `mem_generator_domain_iff_sqrt` | `dom B ⊆ dom √B`; **`(√B)² = B` with domains**: `u ∈ dom B ⇔ u ∈ dom √B ∧ √B u ∈ dom √B`, and then `√B (√B u) = B u` |
| `diffQuot`, `repr_diffQuot`, `slope_bound`, `tendsto_slope` | `t⁻¹ (T(t)u − u)` and its coefficients `t⁻¹(e^{−2t√b_n} − 1) û_n` (`t > 0`); `0 ≤ t⁻¹(e^{−2st} − 1) + 2s ≤ 2s`; `t⁻¹(e^{−2st} − 1) → −2s` as `t ↓ 0` |
| `tendsto_diffQuot` | for `u ∈ dom √B`: **`t⁻¹ (T(t)u − u) → −2√B u` in `L²(S¹)` as `t ↓ 0`** |
| `mem_sqrtGen_domain_of_tendsto` | conversely, **if `t⁻¹ (T(t)u − u) → v` as `t ↓ 0`, then `u ∈ dom √B` and `v = −2√B u`** |
| `generator_iff`, `semigroupGen`, `semigroupGen_iff` | **the generator of `t ↦ T(t)` in the sense of `C₀`-semigroups (domain: the `u` for which the limit exists) is `−2√B`**: `t⁻¹ (T(t)u − u) → v` iff `u ∈ dom √B` and `v = −2√B u`; `semigroupGen := (−2) • √B` has exactly this graph |
| `hol_semigroup_generator` | manuscript form: `T(0) = I`, `T(s + t) = T(s)T(t)`, `‖T(t)‖ ≤ 1`, strong continuity, `‖T(t) − I‖ = 1` (`t > 0`), `T(t) = cfc (evGen t) (B⁻¹)` (`t > 0`), `invSqrt = cfc √· (B⁻¹)`, `√B` self-adjoint with `dom √B = H¹(S¹)`, `Re ⟪u, √B u⟫ ≥ a‖u‖²`, `(√B)² = B` with domains, generator `−2√B` |

## Method

All operators involved are Fourier multipliers or inverses of injective multipliers, so every statement is
reduced to the Fourier coefficients through Parseval (`lp.norm_rpow_eq_tsum` and the isometry
`fourierONB.repr`). Strong continuity: `‖T(t)u − T(t₀)u‖² = ∑_n |e^{−2t√b_n} − e^{−2t₀√b_n}|² |û_n|²`, each
term tends to `0` and is bounded by `|û_n|²`, which is summable; Tannery's theorem
(`tendsto_tsum_of_dominated_convergence`) gives the limit `0`. Generator: for `t > 0` and `s = √b_n ≥ 0`,
`t⁻¹(e^{−2st} − 1) + 2s = t⁻¹(e^{−2st} − 1 + 2st) ∈ [0, 2s]` (from `1 − y ≤ e^{−y} ≤ 1`), so the
coefficients of `t⁻¹(T(t)u − u) + 2√B u` are bounded in modulus by `2√b_n |û_n|`, square summable exactly
when `u ∈ dom √B`; each tends to `0` because `t ↦ e^{−2st}` has derivative `−2s` at `0`
(`HasDerivAt.tendsto_slope_zero_right`). Conversely, the coefficient functional `w ↦ ŵ_n` is continuous,
so a limit `v` has `v̂_n = −2√b_n û_n` (uniqueness of limits along `𝓝[>] 0`); then `∑ b_n |û_n|² =
(1/4) ∑ |v̂_n|² < ∞`, i.e. `u ∈ dom √B`, and `v = −2√B u`. `√B` is the inverse of the bounded,
self-adjoint, injective operator `cfc √· (B⁻¹)` (identified with the multiplier `b_n^{−1/2}` through
`cfc_sqrt_resolvent_mode` of #643 and `multiplier_unique` of #599), hence self-adjoint by #611; its domain,
the identity `(√B)² = B` and the lower bound are coefficient computations, with `b_n ≍ 1 + n²` from #622
(`circleEig_le`, `one_add_sq_le`). `‖T(t) − I‖ ≥ 1 − e^{−2t√b_k}` on `e_k`, and `√b_k → ∞`.

The file selects, by `attribute [local instance high]`, the real algebra structure
`instAlgRealL2Circle` of #643 (restriction of scalars from `ℂ`), so that `cfc` has the same meaning as in
#643 and its lemmas apply verbatim.

## Published results cited, not re-proved

- Continuous functional calculus of bounded self-adjoint operators and its uniqueness: Mathlib, through #643.
- For a positive self-adjoint operator `B`, the uniqueness of its positive self-adjoint square root and the
  identity `h(B) = (h ∘ ι)(B⁻¹)` of the spectral theorem (classical spectral theory of unbounded
  self-adjoint operators). Mathlib has no functional calculus of unbounded operators at the pinned commit:
  `√B` is *defined* here as `(cfc √· (B⁻¹))⁻¹` and proved to be self-adjoint, bounded below by `a`, with
  `(√B)² = B`; that it coincides with the spectral-theorem square root is the cited uniqueness result.

## Not claimed

- A functional calculus of the unbounded operator `B` itself; the equivalence of the Fourier form of
  `H¹(S¹)` with the definition by weak derivatives.
- Any use of the Hille–Yosida or Lumer–Phillips theorem (the generator is computed directly).
- Trace-class membership and basis independence of the diagonal sums (Lidskii; Simon 2005), as before.
- Any Maxwell or geometric statement; the correspondence with the printed display of `eq:hol-integral` in
  `16.tex` (source not in the repository).

## Verification

- Local, pinned toolchain (Mathlib at `0272bbe1`, cache from `lake exe cache get`): the 23 imported
  repository modules (the 22 modules of #643's workflow and `HolonomyFunctionalCalculus20261127`) and the
  new module compile with exit 0; the new module produces no error, warning or `Try this`; its 53
  declarations depend only on `propext`, `Classical.choice`, `Quot.sound` (46 of the 53 lists wrap over
  several lines and were parsed as such); the 464 axiom reports of the imported modules (189 wrapped) contain
  only these three. The audit step of the new workflow was replayed locally on these logs: `SUCCESS: 53
  declarations ( 46 wrapped lists ) and 464 imported reports ( 189 wrapped lists ); standard axioms only`.
- Certifying run: `.github/workflows/m16-hol-semigroup-generator-20261128.yml` (exact-HEAD checkout and SHA
  assertion, pinned toolchain and Mathlib asserted, compilation of the 23 imported modules and of the new
  module, failure on any error, `sorryAx`, `Lean.ofReduceBool`, on any warning or `Try this` in the new
  module and on any non-standard axiom; line-based parser of the axiom reports, so that names with primes and
  wrapped lists are included, with a count check against the report lines; artifact with per-declaration
  axiom lists).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
