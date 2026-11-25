# M16 §14.5 `eq:hol-integral`: operator realisation on `L²(S¹)` of the circle resolvent — 25 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/HolonomyCircleResolvent20261125.lean` (39 audited declarations).

## Starting point

`lean/Manuscript16/CERTIFICATION_SCOPE_20261117_V166_REACTIVE_HOLONOMY.md` lists for
`eq:hol-integral` as remaining: "abstract spectral theorem, trace summability, Tonelli and operator
realisation". The open PR #598 (`HolonomyMomentSeries20261124`) proves summability and the
interchange of sum and integral for the explicit real sequence `b_n = (n − φ)² + a²` and states
that `b_n` is not realised as the spectrum of an operator. No Lean statement in `lean/Manuscript16`
uses `L²(S¹)` or the Fourier basis, and no open PR treats this operator (checked 25 Nov 2026,
00:00 UTC: open PRs #598, #597 (M16 §14.5, scalar), #587, #584, #582, #581, #565, #563, #394
(M11–M14) and #474 (shared nuclear trace on an abstract Hilbert space, M14; not merged, not used
here)). The obligation designated first in the agent's brief, M16 `thm:dirac-maxwell-obstruction-164`
(i)–(ii), is already closed in `main` (#576, #585, #588) and was not re-proved.

This branch is stacked on #598 (head `ab3e60a76e3e3ec490aa8c09c9f244098bc4407f`): it imports
`HolonomyMomentSeries20261124` for the closed forms and must be integrated after #598.

## What is proved

`S¹ = ℝ/2πℤ` (Mathlib `AddCircle (2π)`), `L2Circle = L²(S¹)` for the normalised Haar measure,
`e_n = fourierLp 2 n` (`e_n(θ) = e^{inθ}`), `F = fourierBasis.repr : L²(S¹) ≃ₗᵢ ℓ²(ℤ)`;
`b_n = circleEig a φ n = (n − φ)² + a²`, `a > 0`, `φ` real; `B = (D − φ)² + a²`, `D = −i d/dθ`.

| Declaration | Statement |
|---|---|
| `multiplier d` | bounded operator `F⁻¹ ∘ diag(d) ∘ F` on `L²(S¹)` for a bounded symbol `d : ℤ → ℂ` (`diag`: merged `V166L2SpectralInverse.diagonal`) |
| `multiplier_mode`, `inner_mode_multiplier` | `multiplier d e_n = d n • e_n`; `⟪e_m, multiplier d e_n⟫ = if m = n then d n else 0` |
| `multiplier_unique` | a bounded operator `S` with `S e_n = d n • e_n` for all `n` equals `multiplier d` (density of trigonometric polynomials, Mathlib `span_fourierLp_closure_eq_top`) |
| `multiplier_norm_le`, `norm_le_multiplier_norm` | `‖d n‖ ≤ ‖multiplier d‖ ≤ M` |
| `multiplier_isSelfAdjoint` | real symbol ⇒ `IsSelfAdjoint` |
| `multiplier_injective` | nonvanishing symbol ⇒ injective |
| `multiplier_isCompactOperator` | `{n | ε < ‖d n‖}` finite for all `ε > 0` ⇒ compact (merged `DiracMaxwellCoefficientModel20261124.diagonal_isCompactOperator`) |
| `resolvent a φ` | **the multiplier with symbol `1/b_n`: a bounded operator on `L²(S¹)`** |
| `resolvent_mode`, `resolvent_inverts_on_mode` | `resolvent e_n = b_n⁻¹ • e_n`; `resolvent (b_n • e_n) = e_n` |
| `resolvent_isSelfAdjoint`, `resolvent_injective`, `resolvent_isCompactOperator` | self-adjoint, injective, compact (`resolventSymbol_finite`: `{n | ε < 1/b_n}` ⊆ a finite integer interval) |
| `resolvent_norm_le`, `resolvent_norm_phase_zero` | `‖resolvent a φ‖ ≤ 1/a²`; `‖resolvent a 0‖ = 1/a²` |
| `resolvent_unique` | `resolvent` is the only bounded operator with `S (b_n • e_n) = e_n` for all `n` |
| `modeFun`, `circleMode_ae_eq`, `modeFun_eq` | `modeFun n θ = fourier n (θ mod 2π) = e^{inθ}`; the `L²` class `e_n` is a.e. `fourier n` |
| `modeFun_hasDerivAt`, `deriv_modeFun` | `d/dθ e^{inθ} = i n e^{inθ}` (from Mathlib `hasDerivAt_fourier`) |
| `twistedOp_modeFun` | **`(−d²/dθ² + 2iφ d/dθ + φ² + a²) e^{inθ} = b_n e^{inθ}`**, i.e. `B e_n = b_n e_n` for the differential expression acting on the actual functions |
| `resolvent_diagonal_hasSum` | **`∑_{n∈ℤ} ⟪e_n, resolvent e_n⟫ = (π/a) sinh(2πa)/(cosh 2πa − cos 2πφ)`** (`HasSum` over `ℤ`, with #598 `circle_resolvent_hasSum`) |
| `evanescent a φ t` | the multiplier with symbol `e^{−2t√b_n}`, `t ≥ 0` (`e^{−2t√B}` in the Fourier diagonalisation); `evanescent_mode`, `evanescent_isSelfAdjoint` |
| `evanescent_zero`, `evanescent_add` | `e^{0} = id`; semigroup law `e^{−2(s+t)√B} = e^{−2s√B} ∘ e^{−2t√B}` |
| `evanescent_diagonal_integral` | **`∫₀^∞ z ∑_{n∈ℤ} ⟪e_n, e^{−2z√B} e_n⟫ dz = momentClosed a (πa) (cos 2πφ)`** (Lebesgue integral on `Ioi 0`; with #598 `evanescent_trace_integral`) |
| `resolvent_diagonal_eq_four_integral` | **`Re ∑_n ⟪e_n, resolvent e_n⟫ = 4 ∫₀^∞ z ∑_n ⟪e_n, e^{−2z√B} e_n⟫ dz`** |

Local check (pinned toolchain, 25 Nov 2026): the 14 imported repository modules
(`SharedCore/FredholmCompactParametrix`, `SharedCore/FredholmAtkinson`, `V165TypedGraphSchur`,
`V165GraphNeumann`, `V166CompactTransfer`, `DiracMaxwellObstructionIndex20261124`,
`DiracMaxwellGraphSpace20261124`, `V166L2SpectralInverse`, `V166SpectralCutoffs`,
`DiracMaxwellCoefficientModel20261124`, `V166HolonomyPair`, `ReactiveHolonomyV166`,
`HolonomyEulerProduct20261124`, `HolonomyMomentSeries20261124`) and the new file compile with exit 0;
the new file produces no message (no warning, no error, no `Try this`); its 39 declarations depend
only on `propext`, `Classical.choice`, `Quot.sound`; the 147 axiom reports of the imported modules
contain only these three. Local source SHA-256:
`cb4f6871e3c2dc43528cf429e3dfc1defecf6577344d6d63d2aad8411cb34e2d`. The certifying run is
`.github/workflows/m16-hol-circle-resolvent-20261125.yml` (exact-HEAD checkout, pinned toolchain,
compilation of the 14 imported modules, `#print axioms` audit of 39/39 declarations and 147 imported
reports, failure on any warning or `Try this` message in the new file, artifacts).

## Published results cited, not re-proved

- Fourier Hilbert basis of `L²(S¹)` and density of trigonometric polynomials: Mathlib
  `fourierBasis`, `orthonormal_fourier`, `span_fourierLp_closure_eq_top`.
- Mittag-Leffler expansion of the cotangent and interchange of sum and integral: through #598.

## Not claimed

- The self-adjoint realisation of the unbounded operator `B = (D − φ)² + a²` on its domain `H²(S¹)`
  and the identity `resolvent = B⁻¹` as the inverse of that unbounded operator. The link with the
  differential expression is proved mode by mode (`twistedOp_modeFun` on the functions `e^{inθ}`,
  `resolvent_inverts_on_mode` in `L²`), and the operator is characterised by its action on the
  Fourier basis (`resolvent_unique`).
- That `∑_n ⟪e_n, T e_n⟫` is the trace of `T`: these are diagonal sums in the Fourier basis.
  Trace-class membership and basis independence (Lidskii; Simon 2005) are not formalised (no
  Schatten classes in Mathlib at the pinned commit).
- Any statement on the holonomy of a specific Maxwell field, or any geometric statement.
- The correspondence of the symbols with the printed display `eq:hol-integral` of the 24 Nov 2026
  `16.tex` (circle `ℝ/2πℤ`, `D = −i d/dθ`, `b_n = (n − φ)² + a²`) was not re-read in the source,
  which was not available to this run, and is to be confirmed.
