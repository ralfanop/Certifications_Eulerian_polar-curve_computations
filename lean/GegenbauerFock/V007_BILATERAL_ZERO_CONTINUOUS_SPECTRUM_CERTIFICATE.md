# V007 — Bilateral continuous zero spectrum and inverse ill-posedness

**Scope:** isolated V007 Gegenbauer–Fock research formalization on PR #16. Both Hilbert spaces and both genuine infinite-dimensional Gram operators are retained. The approved V097 manuscript and `main` are not modified; **PR #16 remains DRAFT and MUST NOT BE MERGED** without express approval.

For every real `lam, alpha > 0`, denote the actual coefficient analysis map by `C` and its two positive, compact and selfadjoint Grams by `Gsrc = C†C` on ultraspherical `L²(ν_lam)` and `Gout = CC†` on the complete Gaussian–Fock coefficient Hilbert space. They act on *different* spaces.

## Established theorem hierarchy

1. `TwoSidedGramZeroNonEigen.lean`: zero is in both genuine operator spectra, yet both zero eigenspaces vanish. Previous audited Lean SUCCESS:
   - https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40744819476
2. `TwoSidedGramNotSurjective.lean`, `TwoSidedGramProperDenseRange.lean`, `TwoSidedGramNonclosedRange.lean` establish that **each** Gram has injective, proper, dense, nonclosed image.
3. `TwoSidedGramContinuousSpectrum.lean` defines `IsContinuousSpectralPointAtZero` explicitly by spectrum membership, trivial kernel, dense range and nonsurjectivity; `two_sided_gram_zero_continuous_spectrum` proves this for each Gram. This is a definition of the **classical zero continuous-spectrum criterion** rather than a claim that Mathlib already supplies this exact spectral-subset API.
4. `TwoSidedGramInverseInstability.lean`: for every finite `K : ℝ≥0`, the two theorems `sourceGram_inverse_unbounded_on_range` and `outputGram_inverse_unbounded_on_range` exhibit an actual input with `K * ‖G x‖ < ‖x‖`. Hence inverses defined on the respective ranges have no finite operator-norm/Lipschitz stability bound. Kernel compilation and `#print axioms` audit: **SUCCESS**, build 9106 jobs:
   - https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40754055831
5. `OutputGramApproximateZeroSpectrum.lean`: constructs a unit output-Gram approximate-zero sequence. The consolidated `two_sided_gram_normalized_approximate_zero_sequences` combines it with the previously certified unit source-Gram sequence. Kernel compilation and `#print axioms` audit: **SUCCESS**, build 9107 jobs:
   - https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40754215848
6. `TwoSidedGramNoContinuousReconstruction.lean`: no globally defined exact (including nonlinear) left inverse of either Gram can be continuous at zero. Kernel compilation and `#print axioms` audit: **SUCCESS**, build 9108 jobs:
   - https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40755332247

The successful logs for items 4–6 report only `propext`, `Classical.choice`, `Quot.sound` in the checked declarations, and their audit rejects `sorryAx` and `Lean.ofReduceBool`. A Lean compilation SUCCESS is SHA-scoped: later source modifications are not automatically certified by earlier runs.

## Next independently audited candidate

`TwoSidedGramApproximateZeroNoStrongLimit.lean` is added to demonstrate that normalized approximate-zero sequences in both separate Hilbert spaces have no strong limit. Its isolated workflow is:
- https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/workflows/gegenbauer-fock-two-sided-gram-inverse.yml

**Do not call this last candidate certified until the workflow for its exact source revision finishes SUCCESS and the axiom audit is inspected.**

## Operator-theoretic interpretation

Because the Grams are selfadjoint, injectivity eliminates the zero point spectrum and makes their ranges dense. Since zero still lies in their spectra, neither operator is invertible on its entire Hilbert space; their ranges are proper and nonclosed. The inverses are algebraically defined on those ranges, but are unbounded there. This is not a contradiction: uniquely reconstructible does not mean stably reconstructible.

These statements do **not** identify the two Hilbert spaces, prove that zero is an eigenvalue, or assert any unsupported finite-dimensional spectral truncation.
