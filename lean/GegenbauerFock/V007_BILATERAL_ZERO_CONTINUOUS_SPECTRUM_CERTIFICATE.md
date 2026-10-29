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
  `IsSingularWeylSequenceAtZero` by unit norms, strong convergence
  of Gram images to zero and full weak convergence of test inner
  products, with one witness in each actual Hilbert space.
  **SUCCESS**, 9110 jobs and clean axiom audit at SHA
  `59d3da457ebd09fc4ce91976afcd5379b378e115`:
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40860754934
  This is a certified sequence-level predicate, not an unproved
  equality with a Mathlib essential-spectrum set API.
- `TwoSidedGramZeroNotFredholm.lean` proves each actual Gram is
  **not** `ContinuousLinearMap.IsFredholm` directly from the
  previously certified nonclosed range, connecting to the Fredholm
  definition of essential spectrum without relying on a separate
  singular-Weyl/essential-spectrum API.
  CI: https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40861103876

**The singular Weyl module is certified; the direct non-Fredholm
module remains pending until its own kernel build and axiom audit
return SUCCESS.**

## Update — 29 October 2026: positive spectrum and regularized invertibility verified

The following dedicated Lean 4/Mathlib runs have **completed SUCCESS**,
including the two-standard/three-standard axiom audits with no
`sorryAx` or `Lean.ofReduceBool`:

1. `TwoSidedGramPositiveSpectrum.lean`, SHA
   `3a8009aeefd94d5243810c43efee69a2dd7a4e5d`:
   https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40860557124.
   Both genuine compact Gram spectra lie on the nonnegative real axis;
   each nonzero spectral value is a strictly positive real scalar.
2. `TwoSidedGramNegativeResolvent.lean`, SHA
   `b2510286a8e2438d394146b0fea0a3057afb608e`:
   https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40860919589.
   The entire scalar resolvent sets of the two true Grams coincide,
   and every strictly negative real scalar lies in each resolvent:
   both positive Tikhonov shifts `G + tI`, `t > 0`, are invertible.
3. `TwoSidedGramZeroNotFredholm.lean`, SHA
   `2f2c9c576e3e`:
   https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40861103876.
   Both genuine Grams are non-Fredholm at zero. This supersedes the
   preceding **pending** label for the direct non-Fredholm theorem.
4. `TwoSidedGramWeakConvergence.lean` and
   `TwoSidedGramSingularWeylZero.lean` are separately certified by
   runs 40860310262 and 40860754934 respectively; see the preceding
   checkpoint for exact statement boundaries.

**New quantitative candidate:**
`TwoSidedGramJointSpectralBand.lean` combines positivity, common full
spectrum, and the universal spectral norm bound to enclose all shared
spectral values in the real interval from zero to the *minimum* of
both operator norms. It also establishes a common right-halfplane
resolvent above this minimum bound. Its dedicated workflow is
the workflow `.github/workflows/gegenbauer-fock-gram-joint-spectral-band.yml`;
this candidate must not be called kernel certified before a verified
SUCCESS run and a clean theorem-axiom audit.

PR #16 remains Draft/unmerged, with `main` and approved V097 untouched.

## Update — 29 October 2026: Fredholm essential spectral zero certified

The actual Fredholm essential-spectrum sets are defined as
`fredholmEssentialSpectrum T = {z : ℂ | ¬ ContinuousLinearMap.IsFredholm (T - z • 1)}`.
The two different true Hilbert-space Gram operators `G1=C†C` and
`G2=CC†` satisfy **0∈σess(G1)∩σess(G2)**.

- `TwoSidedGramZeroNotFredholm.lean`: both Grams are non-Fredholm,
  by their previously certified nonclosed ranges.
  **SUCCESS**, 9105 Lean jobs:
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40861103876
- `TwoSidedGramFredholmEssentialSpectrum.lean`: zero belongs to both
  explicitly defined Fredholm essential-spectrum sets. In addition,
  `two_sided_gram_zero_essential_and_singular_weyl` supplies
  independently proven singular Weyl sequences in both Hilbert spaces.
  **SUCCESS**, 9112 Lean jobs, audited SHA
  `5b5ca5d15516418ec92010fbe1e649088cb973c9`:
  https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40864759761

Both success logs include direct `#print axioms` inspections with only
`propext`, `Classical.choice`, `Quot.sound`; neither includes
`sorryAx` or `Lean.ofReduceBool`.

A separate proposed inclusion
`fredholmEssentialSpectrum T ⊆ spectrum ℂ T`, with exclusion of every
strictly negative real scalar for the two positive Grams, is deposited
as `FredholmEssentialSpectrumResolventExclusion.lean` and is subject
to an **independent** Lean workflow audit:
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40865662295

This second inclusion is *not yet certified*. Neither module claims
the stronger equality `σess(Gi) = {0}`. Do not transfer certification
between workflow source SHAs. PR #16 remains Draft/unmerged; `main`
and approved V097 are untouched.

## Update — 29 October 2026: independently checked Fredholm inclusion and Gram trace

**SUCCESS:** the Fredholm essential-spectrum inclusion and exclusion of negative
parameters in `FredholmEssentialSpectrumResolventExclusion.lean`
is independently certified with axiom audit:
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40865662295.
This replaces the preceding *pending* statement, but is **not** a
proof that the entire Fredholm essential spectrum is exactly `{0}`.

**SUCCESS:** the full Gram positive trace-diagonal identities in
`DualGramPositiveTraceDiagonal.lean` passed the dedicated Lean build after
correcting the malformed dependent lambda binder, commit
`c9adac5f5e493d93d0c8187f728ce05a936cf664`:
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40865197477.
These are statements about summability and the diagonal trace in genuine
Hilbert bases, not numerical spectral eigenvalue estimates.

**SUCCESS:** the Gaussian radial-circle bridge also passed its isolated
workflows, including:
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40864894029
and
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40865868626.

**Pending new quantitative enclosure:** The first isolated compilation of
`TwoSidedGramJointSpectralBand.lean`,
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40865087179,
failed because `spectrum.norm_le_norm_of_mem` requires a
`NormOneClass` instance that is not present for general continuous
endomorphisms. The replacement in commit
`f22b3bf0e18f98702eb142a2b6fdfa3a907518bd`
uses `spectrum.norm_le_norm_mul_of_mem` and the separately verified
operator inequality `‖id‖ ≤ 1`, without assuming nontriviality of either
Hilbert space. The dedicated CI is:
https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/40868388808.
A new SUCCESS and standard-axiom audit are required before claiming it
as kernel certified.

The newly attempted enclosure uses the minimum of the **two** Gram
operator norms because their full complex spectra are proven equal,
not because the two operators have been identified.

PR #16 remains Draft/unmerged. Neither `main` nor approved V097
has been modified.
