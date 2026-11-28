# M16 v16.5 §14.2, Proposition 14.2: the Robin resolvent across the bound state and the two-sided simple pole at `t₀ = c − β²` — 28 Nov 2026

Scope: Manuscript 16 only. The LaTeX source is not modified. Manuscripts 11–15 are not touched.
Toolchain: Lean `v4.35.0-rc3`, Mathlib `0272bbe1c093d038d7257ab15306abd58245f9ff`.
New file: `lean/Manuscript16/RobinDirichletSimplePole20261128.lean` (26 audited declarations), SHA-256
`940061c5e2c207bd9b29adcf0562ff8df175197e3a25befacaf2646b792cf184`. It imports `Mathlib` and
`Manuscript16.RobinDirichletBoundState20261127` (#659), hence the merged Robin–Dirichlet modules of #603, #604,
#605, #606, #607, #610, #611, #632, all unchanged in `main` = `58840c220d3b6e8f2b178449bd00c4a948f1ede9`
(branch base, merge of #713) and not re-proved.

## Starting point

The audit note `audits/Manuscript16_v16_5_RobinResolventRankOne_20261116.md` states: "The Robin resolvent has a
simple pole at `a = β`, corresponding to `t = c − β²` … The pole residue in the spectral parameter `t` equals
minus the eigenprojection". #604 and #659 proved the residue from one side only (`t ↑ t₀`, `a ↓ β`), because the
Green operators of #603–#632 and the level independence of #632 are built for `a > β`; the record of #659 lists
as not claimed "the resolvent of `H_R` at levels `t₀ < t < c` and the limit `t ↓ t₀`; that `t₀` is an isolated
point of `σ(H_R)` on its right". This file closes that gap. No open PR touches Manuscript 16 or 17 (checked
28 Nov 2026, 00:55 UTC through the REST API: the open PRs #712, #703, #695, #679, #677, #676, #657, #653, #584,
#474, #394 concern Manuscripts 11–15, `SharedCore` or `SpecialImaginaryPoint`; none of their files lies under
`lean/Manuscript16`, `lean/Manuscript17`, `numerics/arb/m16*`, `numerics/arb/m17*` or `audits/M16_M17*`).

## Statements

`c = ‖κ‖²`, `β > 0`, `t₀ = c − β²`, `L2 = L²((0,∞); ℂ)`; for `a > 0`, `K_D(a) = KDop`,
`K_R(a) = KRop = K_D(a) + P_a`, `P_a = robinDiff = (a − β)⁻¹ |v_a⟩⟨v_a|` (#605; `KRop` is defined for every real
`β`), `KDopT`, `KRopT`, `robinDiffT` their total versions (#604, #659), `HD a t = t + K_D(a)⁻¹`,
`HR a β t = t + K_R(a)⁻¹` (#611, `realisation`), `v_b = vvec b`, `u_β = eigVec β`, `Q = eigProj β` (#604).

| Declaration | Statement |
|---|---|
| `KDop_vvec_of_lt`, `KDop_vvec_ne` | **`K_D(b) v_a = (b² − a²)⁻¹ (v_a − v_b)` for all `a, b > 0`, `a ≠ b`** (#659 had `a < b`; the case `b < a` follows from it and the first resolvent identity of #632 applied to `v_b`, the term `K_D(b) v_b` cancelling) |
| `KRop_apply'`, `inv_sub_inv_robin` | `K_R(a) g = K_D(a) g + (a − β)⁻¹ ⟪v_a, g⟫ v_a`; `(a−β)⁻¹ − (b−β)⁻¹ = (b − a)(a−β)⁻¹(b−β)⁻¹` |
| `KRop_resolvent_identity_ne` | **`K_R(a) − K_R(b) = (b² − a²) K_R(a) K_R(b)` for all `a, b > 0` with `a ≠ β`, `b ≠ β`** (#632 had `a, b > β`): Dirichlet identity of #632, `K_D(a) v_b`, `⟪v_a, K_D(b) f⟫ = ⟪K_D(b) v_a, f⟫` (self-adjointness, #606), `⟪v_a, v_b⟫ = 1/(a+b)` (#604) and the scalar identity above |
| `KRop_injective_ne` | `K_R(a)` injective for `a > 0`, `a ≠ β` (from the identity with `b = β + 1` and #607) |
| `HR_eq_of_level_ne` | **`t + K_R(a)⁻¹ = s + K_R(b)⁻¹`** as `LinearPMap`s whenever `a, b > 0`, `a, b ≠ β`, `t + a² = s + b²` |
| `HR_resolvent_ne` | `K_R(a)` is the bounded two-sided inverse of `H_R − t` for `H_R = s + K_R(b)⁻¹` under the same conditions |
| `aOf_pos_of_lt`, `aOf_sq_of_lt`, `aOf_ne` | for `t < c`: `√(c − t) > 0`, `(√(c − t))² = c − t`, and `√(c − t) ≠ β` if `t ≠ t₀` |
| `smul_robinDiffT_spectral_ne` | `(t − t₀) P_{√(c−t)} = −(a + β) \|v_a⟩⟨v_a\|` for every `t < c`, `t ≠ t₀` (#604 had `t < t₀`) |
| `tendsto_vvec_nhds`, `tendsto_aOf_nhds`, `eventually_lt_c` | `a ↦ v_a` is continuous at `β` from both sides (`‖v_a − v_β‖² = (a−β)²/(2aβ(a+β))`, #604); `√(c − t) → β` as `t → t₀`; `t < c − β²/4` near `t₀` |
| `tendsto_residue_spectral_ne` | `(t − t₀) P_{√(c−t)} → −Q` as `t → t₀`, `t ≠ t₀` |
| `norm_KDopT_le`, `tendsto_smul_KDopT_nhds` | `‖K_D(√(c − t))‖ ≤ 4/β²` for `t < c − β²/4`; `(t − t₀) K_D(√(c − t)) → 0` as `t → t₀` |
| `tendsto_resolvent_residue_ne` | **`(t − t₀) K_R(√(c − t)) → −Q` in operator norm as `t → t₀`, `t ≠ t₀` (both sides)** |
| `regBound`, `tendsto_regBound` | `G(a) = a⁻² + (2aβ(a+β))^{−1/2}(‖v_a‖ + ‖v_β‖) + (a+β)⁻¹‖v_β‖²`, continuous at `β` |
| `eigProj_eq_smul_rankOne`, `robinDiffT_add_smul_eigProj` | `Q = 2β \|v_β⟩⟨v_β\|`; `P_a + (t − t₀)⁻¹ Q = −(β − a)⁻¹(\|v_a⟩⟨v_a\| − \|v_β⟩⟨v_β\|) + (a + β)⁻¹ \|v_β⟩⟨v_β\|` exactly, for `t < c`, `t ≠ t₀` |
| `norm_regular_part_le`, `regular_part_bounded` | **`‖K_R(√(c − t)) + (t − t₀)⁻¹ Q‖ ≤ G(√(c − t))`**, hence bounded on a punctured neighbourhood of `t₀`: the pole is simple |
| `prop14_2_simple_pole` | manuscript form below |

`prop14_2_simple_pole`: fix a level `t₁ < t₀`, `a₁ = √(c − t₁)`, `H_R = HR a₁ β t₁`, `H_D = HD a₁ t₁`
(self-adjoint, #611; independent of `t₁ < t₀`, #632). Then

1. for every `t < c`, `t ≠ t₀`, with `a = √(c − t)`: **`t + K_R(a)⁻¹ = H_R`**; `K_R(a) = K_D(a) + (a − β)⁻¹ |v_a⟩⟨v_a|`
   is the bounded two-sided inverse of `H_R − t` (for `t₀ < t < c` the rank-one coefficient `(a − β)⁻¹` is
   negative); `(H_R − t)⁻¹ − K_D(a) = (a − β)⁻¹ |v_a⟩⟨v_a|`; and `(H_R − t)⁻¹ u_β = (t₀ − t)⁻¹ u_β`;
2. **for real `λ < c`: `λ` is an eigenvalue of `H_R` if and only if `λ = t₀`**;
3. for every `t < c`: `t + K_D(√(c − t))⁻¹ = H_D` and `K_D(√(c − t))` is the bounded two-sided inverse of `H_D − t`;
4. **`(t − t₀)(H_R − t)⁻¹ → −Q`** in operator norm as `t → t₀`, `t ≠ t₀`;
5. **`(H_R − t)⁻¹ + (t − t₀)⁻¹ Q` is bounded** on a punctured neighbourhood of `t₀`.

Hence, in the sense of bounded two-sided inverses, every real `λ < c` other than `t₀` is a resolvent point of
`H_R`, `t₀` is an eigenvalue, isolated in `(−∞, c)` on both sides, and the resolvent has a simple pole there
with residue `−Q`, `Q` the orthogonal projection onto `ker(H_R − t₀)` (#659). Every real `λ < c` is a resolvent
point of `H_D`.

## Method

For `a ≠ b`, `K_D(a) − K_D(b) = (b² − a²) K_D(a) K_D(b)` (#632) applied to `v_a` with `K_D(b) v_a` known for `a < b`
(#659) gives `K_D(a) v_b = K_D(b) v_a`, the unknown `K_D(a) v_a` cancelling. Expanding `K_R(a) K_R(b) f` with
`K_R = K_D + P`, the four terms are `K_D(a) K_D(b) f`, `(b − β)⁻¹ ⟪v_b, f⟫ K_D(a) v_b`,
`(a − β)⁻¹ ⟪K_D(b) v_a, f⟫ v_a` and `(a − β)⁻¹ (b − β)⁻¹ (a + b)⁻¹ ⟪v_b, f⟫ v_a`; with the Dirichlet identity the
difference `K_R(a) f − K_R(b) f − (b² − a²) K_R(a) K_R(b) f` reduces to a combination of `v_a`, `v_b` whose
coefficients vanish by `(a−β)⁻¹ − (b−β)⁻¹ = (b − a)(a−β)⁻¹(b−β)⁻¹` (`linear_combination (norm := module)`).
The two orderings of this identity are the hypotheses of `realisation_eq_of_resolvent_identity` (#632), which
identifies `t + K_R(a)⁻¹` with `s + K_R(b)⁻¹`; `resolvent_of_eq` (#632) then gives the two-sided inverse. For the
pole, `t − t₀ = (β − a)(β + a)` turns `(t − t₀) P_a` into `−(a + β) |v_a⟩⟨v_a|` and the regular part into
`−(β − a)⁻¹(|v_a⟩⟨v_a| − |v_β⟩⟨v_β|) + (a + β)⁻¹ |v_β⟩⟨v_β|`, whose norm is at most
`(2aβ(a+β))^{−1/2}(‖v_a‖ + ‖v_β‖) + (a + β)⁻¹ ‖v_β‖²` by `‖|x⟩⟨x| − |y⟩⟨y|‖ ≤ ‖x − y‖(‖x‖ + ‖y‖)` and the exact
distance `‖v_a − v_β‖ = |a − β|/√(2aβ(a+β))` (#604).

## Published results cited (not re-proved)

- As in #659: the orthogonal projection onto `ker(H − λ)` of a self-adjoint operator `H` is its spectral
  projection `E_H({λ})` (spectral theorem for unbounded self-adjoint operators, e.g. Reed–Simon, *Methods of
  Modern Mathematical Physics I*, Ch. VIII; not in Mathlib at the pinned commit). The resolvent set is used here
  only in the sense of bounded two-sided inverses, as in #632 and #659.

## Not claimed

- The pointwise kernel identity `K_R(a) f = ∫₀^∞ G_R(·,w) f(w) dw` for `a < β` (proved for `a > β` in #603/#605);
  here `K_R(a)` is the operator `K_D(a) + (a − β)⁻¹ |v_a⟩⟨v_a|`.
- The essential spectrum `[c, ∞)` of `H_D`, `H_R`, i.e. that no `λ ≥ c` is a resolvent point.
- Identification of `H_D`, `H_R` with the `H²(0,∞)` realisations; essential self-adjointness on the cores of
  #610; Schatten-ideal membership; any Maxwell identification.
- Correspondence with the printed Proposition 14.2 of `16.tex` (source not in the repository).

## Verification

Local run on the pinned toolchain (`lake env lean -o …`, Mathlib cache of the pinned commit): the 9 imported
Robin–Dirichlet modules recompiled with exit 0 and no error; the new module compiled with exit 0, no error, no
warning, no `Try this`; 26 declarations (7 wrapped axiom lists) and 318 imported reports (56 wrapped lists), each
limited to `propext`, `Classical.choice`, `Quot.sound`. The audit step of the new workflow was replayed locally on
these logs: `SUCCESS: 26 declarations ( 7 wrapped lists ) and 318 imported reports ( 56 wrapped lists ); standard
axioms only`. No `sorry`, `admit`, `axiom`, `unsafe`, `implemented_by` or `extern` in the new module or its local
dependencies.

Certifying run: `.github/workflows/m16-robin-simple-pole-20261128.yml` on the exact PR head (exact-HEAD checkout,
pinned toolchain and Mathlib asserted, compilation of the 9 imported modules and of the new module, failure on any
error, `sorryAx`, `Lean.ofReduceBool`, and on any warning in the new module, line-based axiom parser with count
checks so that names with primes and wrapped lists are included, artifacts). Not yet run when this record was
written.
