# M16 §13 `eq:mixed-schatten-164`: sharp Schatten threshold of the coefficient-space `L₀⁻¹` — 24 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/DiracMaxwellSchattenThreshold20261124.lean` (19 audited theorems).
Depends on #588 (`DiracMaxwellCoefficientModel20261124`, `V166L2SpectralInverse`), whose commit
`26feb5138136e592551caf480c471b08d5dec239` is the parent of this branch.

## Starting point

#588 realizes `L₀ = W_R ⊕ D₃` on `ℓ²(MixedIndex, ℂ)` and proves that its ambient inverse is
`R₀ = diag(w)`, `w = mixedWeight`. The register and #588 listed `L₀⁻¹ ∈ S_p ⇔ p > 3`
(`eq:mixed-schatten-164`) as open. The analytic plan is the one recorded in
`audits/Manuscript16_v165_Section13_SchattenShell_20261117.md` (obligations A and B).

## What is proved

| Declaration | Statement |
|---|---|
| `abs_diracWeight`, `dirac_shell_tsum` | Dirac shell `n`: `∑ |wᵢ|ᵖ = 2(n+1)(n+2)(n + 3/2)^{−p}` (both signs, multiplicity `(n+1)(n+2)`) |
| `dirac_summable_iff` | `∑_{Dirac} |wᵢ|ᵖ < ∞ ⇔ p > 3`, every real `p`; for `p ≤ 3` the shells dominate `(32/45) n⁻¹` |
| `shell_bound` | `a, c ≥ 1`, `0 < L ≤ a + c`, `p ≥ 0` ⇒ `(4ac)^{−p} ≤ (2L)^{−p}(a^{−p} + c^{−p})` |
| `abs_maxwellWeight`, `maxwell_le_majorant` | `|wᵢ| = 1/(4|k||ℓ+k|)` and the pointwise majorant on the Maxwell mode `(ℓ, k)`, using `|k| + |ℓ+k| ≥ ℓ` |
| `shifted_summable`, `shifted_tsum`, `maxwellMajorant_summable`, `maxwellMajorant_tsum` | `∑_{n∈ℤ} |ℓ+n|^{−p} = ∑_{n∈ℤ} |n|^{−p}` (`p > 1`) |
| `maxwell_fiber_summable`, `maxwell_fiber_tsum_le` | shell `ℓ = l + 2` summable, with sum `≤ 2(ℓ²−1)(2ℓ)^{−p} · 2∑_{n∈ℤ}|n|^{−p}` |
| `maxwell_summable` | `∑_{Maxwell} |wᵢ|ᵖ < ∞` for `p > 3` (comparison with `∑ ℓ^{2−p}`) |
| `mixedWeight_summable_iff` | **`∑_{i ∈ MixedIndex} ‖wᵢ‖ᵖ < ∞ ⇔ p > 3`, for every real `p`** |
| `mixedWeight_memℓp_iff` | `w ∈ ℓᵖ ⇔ p > 3` for every real `p > 0` (Mathlib `Memℓp`) |
| `L0_resolvent_weights_memℓp_iff` | the ambient inverse of the #588 `L₀` is `diag(w)`, and `w ∈ ℓᵖ ⇔ p > 3` |

Local check (pinned toolchain): the ten imported project modules and the new file compile with
exit 0, no warning in the new file; all 19 theorems depend only on `propext`,
`Classical.choice`, `Quot.sound`; the 107 axiom reports printed by the imported modules contain
only these three. Source SHA-256 at this commit:
`71335d9d9d9f8b67de5b17af4a0fbfa699787b668bae70204f19d8bfff59d6b0`. Certifying run:
`.github/workflows/m16-dirac-maxwell-schatten-threshold-20261124.yml` (exact-HEAD checkout,
pinned toolchain, rebuild of the imported modules, `#print axioms` audit, artifacts).

## Published results cited, not formalized

- A diagonal operator `diag(w)` on `ℓ²` has singular values the moduli `|wᵢ|`, hence
  `diag(w) ∈ S_p ⇔ w ∈ ℓᵖ`; `S_p` is a two-sided ideal of `B(X)` (Simon, *Trace Ideals and Their
  Applications*, 2nd ed., AMS 2005, Ch. 2). Mathlib at the pinned commit has no Schatten classes.
  With these inputs, `mixedWeight_memℓp_iff` gives `L₀⁻¹ ∈ S_p ⇔ p > 3`, and the ideal property
  transfers it to `L⁻¹ = L₀⁻¹(I + E L₀⁻¹)⁻¹` for `‖E‖ < 3/2`. Neither step is a Lean theorem here.
- As in #588, the unitary identification of `ℓ²(MixedIndex)` with `R ⊕ L²(S³; Σ)` is a published
  input; no geometric statement on `S³` is derived.

## Residual obligations

Every `det₄` statement (`eq:mixed-det4-164`, `eq:mixed-det4-criterion-164`).
