# M16 v16.5 §14.2, Proposition 14.2: self-adjoint operators `H_D`, `H_R` on `L²(0,∞)` whose resolvents at `t` are the Green operators — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletRealisation20261125.lean` (23 audited declarations), SHA-256
`2cfefd3712856c16fc45e316548d422981a02382f55fccf52e6424172990d9ab`. It imports `Mathlib`,
`Manuscript16.RobinDirichletInjective20261125` (PR #607, head `ee465b9c095abdf2e0ca6705a47f3e120633ed8d`,
source SHA-256 `e2ac547e5743055dede0269dce067e1efca99d7d75a811c77dbdb5535e04e7bb`) and
`Manuscript16.RobinDirichletWeakResolvent20261125` (PR #610, head `4844a0e49d63522c6216f71f7cd20fdca14edac5`,
source SHA-256 `faa42c88d1ad1e6ebb6bee64662165c844859351513d9432e6cc327ef0401403`); through them it uses
#606, #605 and #603. The branch is the merge of the #610 and #607 branches (clean merge, no conflict)
plus one commit. Nothing of #603, #605, #606, #607, #610 is re-proved.

## Starting point

The analytic audit note `audits/Manuscript16_v16_5_RobinResolventRankOne_20261116.md` lists among the open
Lean obligations of Proposition 14.2 the **self-adjoint Robin domain**, and every PR of the #603–#610 stack
lists the self-adjoint realisations `H_D`, `H_R` and the identification `KDop = (H_D − t)⁻¹`,
`KRop = (H_R − t)⁻¹` as not claimed. No open PR treats them (checked 25 Nov 2026, 09:55 UTC and again before pushing: #597–#601
concern §14.5, #602 the free line of §14.1, #603–#607 and #610 the items above, #474 `SpecialImaginaryPoint`
and `SharedCore`, the others M11–M14). The first obligation of the run brief,
`thm:dirac-maxwell-obstruction-164` (i)–(ii), is closed in `main` by #576 (with #585, #588) and was not
re-proved.

## Statements

`c = ‖κ‖²`, `β > 0`, `t < c − β²`, `a = √(c − t)`; `L²(0,∞)` with Lebesgue measure; `K_D = KDop`,
`K_R = KRop` the integral operators of the printed kernels (#605).

| Declaration | Statement |
|---|---|
| `realisation K t` | for bounded `K`, the Mathlib `LinearPMap` with graph `{(K f, f + t K f)}`, i.e. `t + K⁻¹` on `ran K` |
| `realisation_domain`, `realisation_apply_K` | domain `= ran K`; `(t + K⁻¹)(K f) = f + t K f` (`K` injective) |
| `realisation_sub_K`, `K_realisation_sub` | `(H − t)(K f) = f` for every `f`; `K((H − t)u) = u` for every `u` in the domain |
| `realisation_isSelfAdjoint` | `K` bounded, self-adjoint, injective, `t` real ⇒ `t + K⁻¹` is self-adjoint (`IsSelfAdjoint`, i.e. equal to its `LinearPMap.adjoint`; dense domain) |
| `HD`, `HR` | `H_D = t + K_D⁻¹`, `H_R = t + K_R⁻¹` |
| `HD_isSelfAdjoint`, `HR_isSelfAdjoint` | `H_D`, `H_R` self-adjoint on `L²(0,∞)` |
| `HD_domain`, `HR_domain` | `dom H_D = ran K_D`, `dom H_R = ran K_R` |
| `HD_resolvent`, `HR_resolvent` | `(H_D − t)⁻¹ = K_D`, `(H_R − t)⁻¹ = K_R`: both one-sided inverse identities on all of `L²(0,∞)` and on the domain |
| `HD_core`, `HR_core` | every `C²` test function with compact support and `φ(0) = 0` (resp. `φ'(0) = −β φ(0)`) lies in `dom H_D` (resp. `dom H_R`) and `H φ = −φ'' + c φ` a.e. on `(0,∞)` |
| `prop14_2_selfadjoint_realisation` | manuscript form: all of the above, and `(H_R − t)⁻¹ − (H_D − t)⁻¹ = K_R − K_D = robinDiff = (a − β)⁻¹ |v_a⟩⟨v_a|` (`KRop_sub_KDop` of #605) |

The remaining declarations are the graph lemmas (`mem_graphSub`, `graphSub_fst_eq_zero`, `realisation_graph`,
`mem_realisation_domain`, `K_mem_domain`), dense range (`denseRange_of_isSelfAdjoint'`,
`realisation_dense_domain`), symmetry (`inner_K_symm`) and the a.e. identity `toLp_Hloc_add_ae`
(`−φ'' + a²φ + tφ = −φ'' + cφ`).

## Method

Part A is the elementary graph computation behind the standard fact that `t + K⁻¹` is self-adjoint when `K`
is bounded, self-adjoint and injective and `t` is real; it is proved only as glue, through Mathlib's
characterisation of the adjoint graph (`LinearPMap.adjoint_graph_eq_graph_adjoint`,
`Submodule.mem_adjoint_iff`): `(x₁, x₂)` is orthogonal (in the skew sense) to every `(K f, f + t K f)` iff
`x₁ + t K x₁ − K x₂ = 0`, i.e. iff `(x₁, x₂) = (K g, g + t K g)` with `g = x₂ − t x₁`. The domain `ran K` is
dense because `(ran K)^⊥ = ker K = 0`. Part B instantiates it with `K_D`, `K_R`, using self-adjointness (#606)
and injectivity (#607); the core statements are the left-inverse identities `K(−φ'' + a²φ) = φ` of #610. No
Sobolev space, trace theorem, Fourier transform or spectral theorem is used.

## Not claimed

- That `H_D`, `H_R` coincide with the realisations of `−d²/dz² + c` on `{u ∈ H²(0,∞) : u(0) = 0}` and
  `{u ∈ H²(0,∞) : u'(0) = −β u(0)}` (no trace theorem, no Sobolev space); essential self-adjointness of
  `−d²/dz² + c` on the two cores (which would identify `H_D`, `H_R` as the closures of the core operators).
- Independence of `H_D`, `H_R` from the level `t` at which they are built (it would follow from the resolvent
  identity `K(t₁) − K(t₂) = (t₁ − t₂) K(t₁) K(t₂)` for the Green operators, or from essential
  self-adjointness on the cores; neither is proved here).
- The essential spectrum; Schatten-ideal membership; any Maxwell or geometric identification.
- The match with the printed Proposition 14.2 of the current `16.tex` still has to be checked against the
  source, which was not available to this run.

## Verification

- Local, pinned toolchain (Mathlib checked out at `0272bbe1` in `.lake/packages/mathlib`, cache from
  `lake exe cache get`): the five imported modules and the new module compile with exit 0; the new module
  produces no error, warning or `Try this`; 23/23 declarations depend only on `propext`, `Classical.choice`,
  `Quot.sound`. The compile-and-audit step of the new workflow was run locally with success
  (`SUCCESS: 23 theorems and 196 imported declarations; standard axioms only`).
- Certifying run: `.github/workflows/m16-robin-dirichlet-realisation-20261125.yml` (exact-HEAD checkout and
  SHA assertion, pinned toolchain and Mathlib pin asserted, compilation of the five imported modules and of the
  new module, failure on any error, warning, `Try this`, `sorryAx`, `Lean.ofReduceBool` or non-standard
  axiom, artifact with per-declaration axiom lists).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
