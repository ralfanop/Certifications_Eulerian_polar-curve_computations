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

The successful logs for the independently audited modules report only `propext`,
`Classical.choice`, and `Quot.sound` in checked declarations; they reject
`sorryAx` and `Lean.ofReduceBool`. Every claim remains SHA-scoped.

7. `TwoSidedGramApproximateZeroNoStrongLimit.lean`: both normalized
   approximate-null sequences have no strong limit. Checked in full by
   Lean 4 plus `#print axioms`: **SUCCESS** (9108 jobs):
   - https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40756217237
8. `TwoSidedGramInverseOnRangeDiscontinuous.lean`: for each Gram
   the exact inverse **on its actual range equipped with the induced
   topology** is discontinuous at zero, with no global inverse extension
   assumption. The first CI exposed a subtype-zero proof mismatch;
   that issue was fixed and the source independently rechecked by Lean 4
   plus `#print axioms`: **SUCCESS** (9108 jobs):
   - https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40761338859
9. `TwoSidedGramNoStronglyConvergentSubsequence.lean`: for each
   normalized approximate-zero sequence, **every strictly increasing
   subsequence fails to converge in norm**. Kernel compilation and
   `#print axioms` audit: **SUCCESS** (9108 jobs):
   - https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40852729755

## Next independently audited candidate

`TwoSidedGramWeakOnDenseRange.lean` establishes vanishing of the
inner products with **every test vector belonging to the range**
of the respective selfadjoint Gram. Both images are dense, so the
statement supplies the exact dense-test component for a later full
weak-convergence theorem. It does not claim to have formalized
weak-topology convergence against arbitrary Hilbert vectors.

The dedicated CI is:
- https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40853101401

The dedicated workflow above completed **SUCCESS** with 9108 Lean jobs,
and the direct `#print axioms` inspection confirms only `propext`,
`Classical.choice`, `Quot.sound` for all three declarations. This
certifies convergence against the two **dense range** test families,
not yet every Hilbert test vector.

Full weak convergence is formalized separately in
`TwoSidedGramWeakConvergence.lean` using uniform unit norms and
Cauchy–Schwarz for the dense-range extension. The first CI exposed
three Lean elaboration errors (operator coercion and the metric
`∃ N, ∀ n ≥ N` form); the source was corrected in SHA
`77285f669ee30b5b6735441310daccc15e95846b`.
The new pending kernel/audit run is:
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40855929809

**Do not call the full-weak-convergence candidate certified without
a successful CI and an inspection of its actual `#print axioms` logs.**

## Operator-theoretic interpretation

Because the Grams are selfadjoint, injectivity eliminates the zero point spectrum and makes their ranges dense. Since zero still lies in their spectra, neither operator is invertible on its entire Hilbert space; their ranges are proper and nonclosed. The inverses are algebraically defined on those ranges, but are unbounded there. This is not a contradiction: uniquely reconstructible does not mean stably reconstructible.

These statements do **not** identify the two Hilbert spaces, prove that zero is an eigenvalue, or assert any unsupported finite-dimensional spectral truncation.


## Update — 29 October 2026: exact bilateral spectrum

The pinned Lean 4/Mathlib workflow
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40852466607
completed **SUCCESS** for code at SHA `a25efdbad1d60d6f4c5ccd3eb16f664529f7c389`.

- `TwoSidedGramSpectrumEquality.lean` proves
  `two_sided_gram_hasEigenvalue_iff`: equal nonzero point spectra;
  `two_sided_gram_nonzero_spectrum_iff`: equal nonzero *operator*
  spectra by Mathlib's compact Fredholm alternative; and
  `two_sided_gram_spectrum_eq`: equality of the **entire complex spectra**
  of the concrete operators `C†C` and `CC†`, including zero.
- The corresponding dedicated build and theorem-axiom checks passed.
  This theorem does **not** identify the underlying Hilbert spaces and
  does **not** claim that `C` is surjective.
- `TwoSidedGramPositiveSpectrum.lean` attempts the stronger claim
  that the common spectrum is real and nonnegative, with strictly
  positive nonzero values. Its earlier failed run
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40852515575
  reported an expression mismatch between `Complex.re` and
  `RCLike.re`. The correction was committed as
  `aabdfbc73c897973aec38fb1876953c16ed9e32a`.
  The recheck is
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40855060907;
  **do not claim its success unless that run actually completes SUCCESS**.
- The independently compiled Weyl-sequence geometry and dense-range
  testing is recorded in successful run
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40853101401.
  The later full weak-convergence strengthening is a **separate**
  candidate awaiting the dedicated run
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40855092208.

**Independent Gaussian area work:** developments in the intrinsic
Gaussian Bargmann–Fock (L^2) realization are on the same PR branch
but are separate from the bilateral Gram-spectrum theorem.
Never transfer certification from a successful Gram workflow to an
unverified Gaussian module, or conversely.

**Repository invariant:** PR #16 stays Draft and unmerged; approved V097
and `main` remain untouched.

## Update — 29 October 2026: full weak convergence and essential-spectrum candidates

The **full test-vector weak convergence** theorem is now independently
kernel-certified at source commit `654192d18507894e043033b7143c8d5960c4fac1`:
- `TwoSidedGramWeakConvergence.lean` —
  `sourceGram_unit_approximate_zero_weakly_null`,
  `outputGram_unit_approximate_zero_weakly_null`, and the bilateral theorem.
- SUCCESS, 9109 Lean jobs, clean three-standard-axiom audit:
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40860310262
- The sequence vectors are normalized, their actual Gram images tend to
  zero in norm, and **every** complex inner product with a Hilbert test
  vector tends to zero. The density argument uses uniform unit norms
  and Cauchy–Schwarz; no assertion of strong convergence of the
  original sequences is made.

Two further dedicated modules are deposited and must be checked separately:
- `TwoSidedGramSingularWeylZero.lean` explicitly defines
  `IsSingularWeylSequenceAtZero` by the three preceding properties,
  with one witness in each true Hilbert space. This is a sequence-level
  predicate, not an unproved equality with a Mathlib spectral set.
  CI: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40860754934
- `TwoSidedGramZeroNotFredholm.lean` proves each actual Gram is
  **not** `ContinuousLinearMap.IsFredholm` directly from the
  previously certified nonclosed range, connecting to the Fredholm
  definition of essential spectrum without relying on a separate
  singular-Weyl/essential-spectrum API.
  CI: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40861103876

**Do not mark either additional module as certified until its
individual Lean kernel build and axiom audit return SUCCESS.**
