# M16 v16.5 §14.2, Proposition 14.2: the Green operators invert `−d²/dz² + a²` on the Dirichlet and Robin cores; weak resolvent identity on all of `L²(0,∞)` — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletWeakResolvent20261125.lean` (36 audited declarations), SHA-256
`faa42c88d1ad1e6ebb6bee64662165c844859351513d9432e6cc327ef0401403`. It imports `Mathlib` and
`Manuscript16.RobinDirichletPositive20261125` (PR #606, head `bfbce14106db70d48952e00544ac1ab01dadbe65`,
source SHA-256 `bdfd818ada54b17c72df2a031a06fde742f6c5f8db029cc61a3228924b3e681c`), which imports
`Manuscript16.RobinDirichletL2Bounded20261125` (PR #605, `303e9028…`) and, through it,
`Manuscript16.RobinDirichletRankOne20261125` (PR #603, `78663893…`). This branch is stacked on #606
(and therefore on #605 and #603). It is independent of #604 and #607. Nothing of #603, #605, #606 is
re-proved.

## Starting point

The analytic audit note `audits/Manuscript16_v16_5_RobinResolventRankOne_20261116.md` lists among the
open Lean obligations of Proposition 14.2 the **Green-kernel distributional jump**, i.e.
`(−∂_z² + a²) G(·, w) = δ_w` with the boundary condition. #603 treats only classical solutions for
continuous data; #603, #605, #606 and #607 all list the relation between `KDop`, `KRop` and the
differential operator on all of `L²(0,∞)` as not claimed. No open PR treats this (checked 25 Nov 2026,
09:05 UTC: #597–#601 concern §14.5, #602 the free line `ℝ` of §14.1, #603–#607 the items above, #474
`SpecialImaginaryPoint`, the others M11–M14). The first obligation of the run brief,
`thm:dirac-maxwell-obstruction-164` (i)–(ii), is closed in `main` by #576, #585 and #588 and was not
re-proved.

## Statements

A *test function* is a `C²` function `φ : ℝ → ℝ` with compact support (`IsTest`); `Hloc a φ = −φ'' + a² φ`.
Dirichlet core: `φ(0) = 0`. Robin core: `φ'(0) = −β φ(0)`, with `β < a`.

| Declaration | Statement |
|---|---|
| `exists_test_mem_cores` | the cores are not empty: a `C^∞` bump vanishing on `(−∞,1)` with `φ(3) = 1` lies in both |
| `abs_greenD_le_inv` | `|G_D(z,w)| ≤ 1/(2a)` for `z, w ≥ 0` |
| `abs_solD_le`, `bounded_solD`, `bounded_solR` | `u_D`, `u_R` bounded on `[0,∞)` for continuous `f ∈ L¹(0,∞)` with `e^{−aw} f ∈ L¹` |
| `solD_Hloc`, `solR_Hloc` | `u_D[−φ'' + a²φ] = φ`, `u_R[−φ'' + a²φ] = φ` on `[0,∞)` (uniqueness theorems of #603) |
| `KD_Hloc`, `KR_Hloc` | `(K_D(−φ'' + a²φ))(z) = φ(z)`, `(K_R(−φ'' + a²φ))(z) = φ(z)` for every `z ≥ 0` |
| `KDop_Hloc`, `KRop_Hloc` | `K_D(−φ'' + a²φ) = φ`, `K_R(−φ'' + a²φ) = φ` in `L²(0,∞)`: left inverse on the cores |
| `integral_greenD_Hloc`, `integral_greenR_Hloc` | `∫₀^∞ G(z,w)(−φ''(z) + a²φ(z)) dz = φ(w)` for every `w ≥ 0`: `(−∂_z² + a²)G(·,w) = δ_w` on `(0,∞)` in the sense of distributions, with the boundary condition of the core |
| `inner_Hloc_KDop`, `inner_Hloc_KRop` | `⟪(−d² + a²)φ, K f⟫ = ⟪φ, f⟫` for **every** `f ∈ L²(0,∞)` (self-adjointness from #606) |
| `weak_KD`, `weak_KR` | `∫₀^∞ (−φ'' + a²φ)(z) (K f)(z) dz = ∫₀^∞ φ(z) f(z) dz` for every `f ∈ L²(0,∞)`: `K_D f`, `K_R f` solve `−u'' + a²u = f` weakly |
| `Hloc_aOf` | with `a = √(c − t)`: `−φ'' + a²φ = (−d²/dz² + c)φ − tφ` |
| `prop14_2_weak_resolvent` | manuscript form (`c = ‖κ‖²`, `β > 0`, `t < c − β²`, `a = √(c − t)`) of all the above |

The remaining declarations are the supporting lemmas on test functions (`C²` regularity, compact support,
`L²`/`L¹` membership, boundedness).

## Method

For `φ` in the Dirichlet (Robin) core, `φ` is a bounded classical solution of `−u'' + a²u = ψ`,
`ψ = −φ'' + a²φ`, with the Dirichlet (Robin) condition; `ψ` is continuous with compact support, so the
variation-of-parameters solution `u_D[ψ]` (`u_R[ψ]`) of #603 is bounded by `(2a)⁻¹ ∫₀^∞ |ψ|` (plus
`|C_ψ|/(a−β)` for Robin), and the uniqueness theorems of #603 give `u[ψ] = φ` on `[0,∞)`. With #603's
`K_D ψ = u_D[ψ]` this is the left-inverse identity; the kernel identity follows from the symmetry
`G(z,w) = G(w,z)`. The weak identity for arbitrary `f ∈ L²` is `⟪ψ, K f⟫ = ⟪K† ψ, f⟫ = ⟪K ψ, f⟫ = ⟪φ, f⟫`,
using the self-adjointness of `K_D`, `K_R` proved in #606. No Sobolev space, trace theorem, Fourier
transform or spectral theorem is used.

## Not claimed

The self-adjoint realisations `H_D`, `H_R` on `H²(0,∞)`; essential self-adjointness of `−d²/dz² + c` on
the two cores; hence the identification `KDop = (H_D − t)⁻¹`, `KRop = (H_R − t)⁻¹` as resolvents of
self-adjoint operators (what is proved is that `K` is a left inverse of `−d² + a²` on the core and that
`K f` is a weak solution for every `f ∈ L²`); the essential spectrum; Schatten-ideal membership; any
Maxwell or geometric identification. The match with the printed Proposition 14.2 of the current `16.tex`
still has to be checked against the source, which was not available to this run.

## Verification

- Local, pinned toolchain (Mathlib checked out at `0272bbe1` in `.lake/packages/mathlib`, cache from
  `lake exe cache get`): the three imported modules and the new module compile with exit 0; the new module
  produces no error, warning or `Try this`; 36/36 declarations depend only on `propext`,
  `Classical.choice`, `Quot.sound`. The compile-and-audit step of the new workflow was run locally with
  success (`SUCCESS: 36 theorems and 143 imported declarations; standard axioms only`).
- Certifying run: `.github/workflows/m16-robin-dirichlet-weak-resolvent-20261125.yml` (exact-HEAD checkout
  and SHA assertion, pinned toolchain and Mathlib pin asserted, compilation of the three imported modules
  and of the new module, failure on any error, warning, `Try this`, `sorryAx`, `Lean.ofReduceBool` or
  non-standard axiom, artifact with per-declaration axiom lists).
- No Arb/FLINT certificate is involved (exact statements; no precision claim).
