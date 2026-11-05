# V007 — Strong spectral-cutoff regularization and its sharp uniform obstruction

## Scope

This note concerns the genuine infinite-dimensional compact Gegenbauer–Fock operator
`C_{λ,α} : H_λ=L²(ν_λ;ℂ) → K_α`, for `λ,α>0`. It belongs exclusively
to V007; it does not amend V097. The existing completed singular-Hilbert-basis
theorems are dependencies, not assumptions introduced in this note.

## Exact singular cutoff

Use the certified complete orthonormal Hilbert bases `(u_i)_{i∈I}` of
`H_λ` and `(v_i)_{i∈I}` of `K_α`, with strictly positive real
singular values `σ_i=√μ_i>0` and

`C u_i = σ_i v_i,   C* v_i = σ_i u_i`.

For a finite subset `S⊆I`, define the bounded, finite-rank operator

`R_S^C : K_α → H_λ,     R_S^C F = ∑_{i∈S} σ_i^{-1} ⟨v_i,F⟩ u_i.`

Its pointwise exact reconstruction identity is

`R_S^C C f = ∑_{i∈S} ⟨u_i,f⟩u_i.`

The right side is the orthogonal partial Hilbert expansion of `f`. Since
the source singular family is a *complete Hilbert basis*, these sums converge
unconditionally in `H_λ` as `S` ranges over the directed set of finite
subsets ordered by inclusion:

`R_S^C C f → f` in `H_λ` for every fixed `f`.

This is strong convergence, indexed by a finite-subset net; it does not
by itself assert an explicit natural-number enumeration of `I`.

## Canonical CFC polar root

Write `P=CFC.sqrt(C* C)` for the genuine canonical positive root. The
previously Lean-certified full unitary polar factorization `C=WP`
transfers each cutoff to the root:

`R_S^P = R_S^C W : H_λ → H_λ`.

Then `R_S^P P f = R_S^C C f → f` strongly.

## Actual source Gram

The source Gram `G=C*C=P²` has the same complete source eigenbasis
with positive eigenvalues `μ_i=σ_i²`. Define

`R_S^G g = ∑_{i∈S} μ_i^{-1}⟨u_i,g⟩u_i.`

Then `R_S^G Gf = ∑_{i∈S}⟨u_i,f⟩u_i → f` strongly.

## Sharp distinction: strong versus operator norm

For every finite spectral set `S`, the previously certified theorem
on normalized approximate-null vectors gives

`‖I-R_S^C C‖op ≥ 1`, and similarly for `P` and `G`.

Indeed these errors equal identity minus a finite spectral projection,
and are exactly 1 when the unselected complement is nontrivial.
Thus pointwise strong consistency does not contradict the failure of
uniform recovery on the full unit ball.

## Deterministic error from noisy data

For `F=Cf+η`, the triangle inequality gives

`‖R_S^C F-f‖ ≤ ‖(R_S^C C-I)f‖ + ‖R_S^C‖‖η‖.`

For nonempty `S`, orthonormality yields the exact cutoff stability factor

`‖R_S^C‖ = max_{i∈S} 1/σ_i`.

The bias term tends to zero for every fixed `f`, while the stability
factor can grow for increasingly inclusive spectral sets. Convergence
with nonzero noise therefore requires coupling the cutoff to the noise
level. No bounded global inverse is claimed.

## Lean source and certification boundary

- `CanonicalCFCSpectralCutoffStrongRecovery.lean`: bounded finite-rank
  singular cutoff and strong consistency on the real operator `C`.
- `CanonicalCFCRootPolarCutoffStrongRecovery.lean`: transport of the same
  cutoff family through the certified unitary polar factor.
- `CanonicalCFCSourceGramCutoffStrongRecovery.lean`: direct source-Gram
  spectral cutoff from the two certified diagonal coefficient identities.

Each new theorem is subject to the separately launched GitHub Actions
workflow and an explicit `#print axioms` audit. Do **not** regard a
deposited theorem, an in-progress CI, or an intermediate red CI as a kernel
certificate; only a successful SHA-specific run with permitted axioms
certifies the stated Lean theorem.

Separate future tasks include a countable cutoff enumeration if desired,
quantitative data-noise bounds in Lean, and strong Tikhonov resolvent
consistency `(G+εI)^{-1}G f→f`. The paper-level error decomposition above
is not presented as already kernel certified.

**V007 only; PR #16 stays Draft, without merge. V097 and V170 are untouched.**
