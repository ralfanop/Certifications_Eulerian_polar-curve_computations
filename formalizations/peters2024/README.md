# Phase 5 — 19 November 2026 (current coverage and open obligations)

## Exact-HEAD evidence

PR #452, HEAD `6a966f2b382ca3e75ec00e535aa41128f237856d`, workflow 44515150543, job 135529147281: **SUCCESS**, 8205 build jobs and 9 exact declarations audited (upstream SphereOddDegree.borsuk_ulam plus 8 article-specific bridge declarations), standard axioms only. Artifact 14525013457. The general Borsuk–Ulam proof is credited to HamSandwich. Base job 135529146987 failed before compilation owing to a nonexistent relative cache path, not a Lean theorem error; Phase 5 replaces these paths with module names.

## Phase 5 mathematical increments

Locally compiled in pinned Lean 4.28.0: 11 new declarations, all with standard axiom audit (`lean_phase5_local.log`). WoodhouseContinuity proves the actual unit-circle contour formula (including the printed normalization 1/(2π)), joint angular continuity, continuity of the resulting integral, continuous injective complex coordinates, and the antipodal result conditional only on the previously checked Borsuk–Ulam statement and the explicit continuity of the coordinate maps/integrand. SurfaceHomotopy proves relative homotopy on simply connected spaces and the reversal loop in 3.2 in every topological space. FeynmanKernelContinuity proves continuity of compactly truncated integrals and of any uniform limit of them; it does not claim that the Feynman path integral exists or its approximants converge uniformly. Three further applications in PetersApplications compose the general Borsuk–Ulam bridge with these results; they are candidates pending exact-HEAD CI.

| Article obligation | Current status | Next check |
|---|---|---|
| 1.1, 1.4 | PROVED on prior exact HEAD | Re-audit next commit |
| 2.9, 3.1–3.4, 3.8 | PROVED in explicit sampled-path model (3.3 ambient, not tangent vector field) | Clarify original model, verify base CI |
| 3.5 | PROVED in sampled-path model, prior bridge CI; relative null-homotopy refinement pending | PetersApplications CI |
| 4.5, 4.8, 5.2 | Continuous-path/projection interpretation PROVED; general continuity cannot follow from density | Record assumption; no false implication |
| 5.4, 5.5 | PROVED under continuity of the actual observable; unrestricted arbitrary-map version false | Establish real physical kernel assumptions, or mark NEEDS_CORRECTION |
| 5.6 | CONDITIONAL: actual physical propagator existence and uniform-convergence estimates OPEN; equal spatial length is insufficient for equality | Choose specified dynamics, discretization and convergence theorem |
| Def.6.1, 6.2, 6.3 | Explicit Woodhouse circle family continuity PROVED locally under continuous coordinates and integrand; application CI pending | Verify composition on exact HEAD; particular twistor coordinate maps must meet these premises |
| 6.5 | NEEDS_CORRECTION in general complex contours; checked counterexamples and valid real/collinear/reflection bisection variants | Specify sufficient geometric/analytic assumptions, no claim for arbitrary complex subarcs |

Historical Phase 1–4 entries below retain their original dates and are superseded where Phase 5 supplies new evidence. Numerical certificates (14) remain untouched; no additional finite numerical obligation arises here.

# GitHub CI scope

This directory contains the Lean source and historical local audit logs only. The full numerical archive, its exact balls and reproduction scripts are preserved separately. GitHub CI success for BorsukBridge is documented in Phase 5 above.

# Peters–Alfano–Smith–Tozzi–Vergili (2024): formal audit

## Phase 4 — 19 November 2026: relative homotopy of image loops

The Phase 3 checkpoint (Library version 2, SHA-256
`c48afc3b80b83448b721d64c585131efc8b785e876de781ffe006420c9d7c5da`)
was recovered and rebuilt using Lean 4.28.0 with the same pinned dependencies.
The supplied article PDF has SHA-256
`4735ee65fb5b8a97d78f07861978225ecabbe26c34cc5305e02202b4833dfe66`.

`HomotopyRealization.lean` adds four kernel-checked theorems:

* `real_normed_paths_homotopic`: explicit homotopy relative to both endpoints,
  H(s,t) = p(t) + s • (q(t) − p(t)), in any real normed vector space;
* `sampled_image_loop_nullhomotopic`: a sampled closed path in that space
  is homotopic to the constant path, fixing its basepoint;
* `thm_3_8_nullhomotopic`: strengthens the non-antipodal path conclusion by
  proving genuine null-homotopy of the image loop;
* `thm_3_5_nullhomotopic`: same strengthening for the antipodal result,
  still with the explicit general Borsuk–Ulam premise.

These are new refinements of the formal model, not claims that an arbitrary
curved surface has a linear homotopy. All four print only the three standard
axioms. The four checked modules now contain 40 theorem declarations in total
(30 + 3 + 3 + 4), excluding the eight still-unchecked bridge theorems.
The numerical certificate is unchanged. The expanded base audit and the
new homotopy audit are in `lean_phase4_base.log` and
`lean_homotopy_realization.log`.

Reproduce: `lake build Peters2024 BorsukCore BisectionRepairs HomotopyRealization`.
The upstream general Borsuk–Ulam dependency is pinned and remains OPEN until
its full kernel compilation succeeds. A new full Mathlib cache attempt made
substantial download progress but encountered HTTP 429 again. The next step
is to finish the dependency build in a dedicated GitHub CI environment,
then verify `BorsukBridge` and all its axiom audits. A separate analytic task
is to instantiate Mathlib's `continuous_parametric_integral_of_continuous`
for a precisely specified Woodhouse contour family; the physical Feynman
propagator still requires an independently justified continuity hypothesis.
Neither the corrected theorems nor the previous counterexamples should be
counted as proofs of an unrestricted printed claim.

## Phase 3 — 19 November 2026: corrected bisection (§6.5)

The unrestricted complex bisection claim remains false, as previously proved.
`BisectionRepairs.lean` provides three sufficient conditions in Lean 4.28:

- `line_bisection`: a continuous real coefficient times a fixed vector;
- `affine_line_bisection`: the analogous assertion for increments along an
  affine line, allowing a nonzero initial value;
- `reflection_bisection`: a reflection identity for cumulative increments
  forces the midpoint to bisect the total, even in an arbitrary additive group.

For complex cumulative integrals, view ℂ as a real module. These results do
not assert that any arbitrary Woodhouse contour satisfies the added hypotheses;
that requires an independently specified contour family and proof. Reproduce
with `lake env lean BisectionRepairs.lean` after building `Peters2024`.
The actual check and axiom audit are in `lean_bisection_repairs.log`.
The 14 previously certified Arb balls remain unchanged. No new numerical
evaluation is required by these universal algebraic/topological results.

The general Borsuk–Ulam bridge and the analytic continuity of the physical
observables remain open. See the Phase 2 and Phase 1 records below.

## Phase 2 — 19 November 2026

**Verified locally:** the 30 existing theorem statements have been migrated to
Lean 4.28.0 / Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`;
`BorsukCore.lean` adds three kernel-checked theorem declarations:

- `borsukUlam_zero` — the dimension-zero case;
- `borsukUlam_one` — a direct proof from path connectedness and the intermediate
  value theorem, without an external Borsuk–Ulam assumption;
- `borsukUlam_of_euclidean` — the precise finite-coordinate / Euclidean-space
  transfer in every dimension, with the Euclidean theorem as a stated premise.

Both local checks exited 0 and the printed dependencies contain only `propext`,
`Classical.choice`, `Quot.sound`. The logs are `lean_v428_base.log` and
`lean_borsuk_core.log`. The Lake warning about local Mathlib changes refers
only to the cache downloader's reduced parallelism; no Mathlib proof source
was modified. The previous Arb results are preserved; the exact
dyadic ball file's SHA-256 was checked against the certificate. No new numerical
certification is needed for this topological step.

**Prepared, not yet kernel-verified locally:** `BorsukBridge.lean` supplies the
general Euclidean theorem from upstream `SphereOddDegree.borsuk_ulam`, wraps it
into `thm_1_1`, and removes the Borsuk–Ulam premise from seven dependent article
results (1.4, 3.5, 5.4, 5.5, 5.6 under the separate kernel-continuity premise,
6.2 and 6.3). The mathematical continuity assumptions remain explicit.
The upstream project is [HamSandwich](https://github.com/akopjan/HamSandwich),
Apache-2.0, pinned at commit `76202dbbb6610ffcebbccfbf7a56f833a4c2a376`.
Its exact theorem declaration and matching sphere model were inspected; both
upstream placeholder scans ran successfully. These scans are not a substitute
for the Lean kernel build. The full dependency cache download was interrupted
by HTTP 429 responses; the general-dimensional closure is therefore pending.
We do not claim ownership of the upstream proof.

To reproduce the checked portion with the pinned Phase 2 manifest:

```sh
lake exe cache get Mathlib/Analysis/InnerProductSpace/PiL2.lean Mathlib/Analysis/Normed/Module/Connected.lean Mathlib/Analysis/Normed/Module/Ball/Action.lean Mathlib/Analysis/Normed/Group/BallSphere.lean Mathlib/Topology/MetricSpace/HausdorffDistance.lean Mathlib/Topology/Order/IntermediateValue.lean Mathlib/SetTheory/Cardinal/Order.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum.lean
lake build Peters2024 BorsukCore
```

To check the pending general-dimensional integration:

```sh
lake exe cache get
lake build BorsukBridge
lake env lean BorsukBridge.lean
```

The last command must exit 0 and list only the three standard axioms for all
bridge endpoints, before changing the pending status. The frozen Phase 1 report
below records the original audit and its historical toolchain.

---

## Phase 1 — 16 November 2026 (historical report)

Source: *Geometric realizations of homotopic paths over curved surfaces*,
Filomat 38(3), 793–802, DOI 10.2298/FIL2403793P. This package refers to the
article supplied by the user, not to a revised manuscript. The original is
unchanged. Date: 16 November 2026.

## Scope and status

The article contains 18 numbered theorems, lemmas, propositions and corollaries.
The Lean module distinguishes exact proofs, formal consequences of an explicitly
stated classical result, and corrections under additional hypotheses. No new axiom
is introduced and no result is admitted with a placeholder proof. The proposition
`BorsukUlam n` is **a statement, not a proof** of Theorem 1.1; every dependent result
has that proposition as an explicit hypothesis. The general classical theorem is
not discharged in this version of the audit. This is not an integral certification
of the published article as printed.

The final module contains 30 theorem declarations plus definitions and was
checked locally with Lean 4.19.0 and the pinned Mathlib revision. Exit code 0;
no compiler warnings or errors. `lean_verification.log` records the axiom audit:
the checked declarations rely only on the standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`.

| Article | Lean declaration / assessment |
|---|---|
| 1.1 | `BorsukUlam`: statement on the actual unit Euclidean sphere and finite coordinate space; proof pending. |
| 1.4 | `thm_1_4`: proof from 1.1, including empty closed members of the cover and the last cover member. |
| 2.9 | `prop_2_9`: true on path-connected spaces; on a disconnected space the unqualified statement would fail. |
| 3.1 | `lemma_3_1`, `samples_joined`: a sampled continuous path has connecting subpaths. |
| 3.2 | `thm_3_2`, `loop_visits_turning_point`: a path followed by its reversal, with the intermediate turning point explicitly retained. |
| 3.3 | `thm_3_3`, `position_norm`, `position_not_orthogonal`: ambient position-vector assignment; not a tangent vector field on the sphere. |
| 3.4 | `lemma_3_4`: antipodal points are joined on the sphere for n ≥ 1; no Borsuk–Ulam assumption is used. |
| 3.5 | `thm_3_5`: proof from 1.1 and path-connectedness; the continuous image is a loop and admits a countable sampling. |
| 3.8 | `thm_3_8`: image loop for any two points with equal image; no Borsuk–Ulam assumption needed. |
| 4.5 | `lemma_4_5`, `trajectory_trace_pathConnected`: precise result when a trajectory is a continuous path; not a construction of a physical quantum trajectory. |
| 4.8 | `lemma_4_8`: continuity of a path by definition; `density_does_not_imply_continuity` shows why density of the parameter interval is insufficient. The physical trajectory hypothesis needs independent justification. |
| 5.2 | `lemma_5_2`, `trajectory_projection`: the projection in Definition 5.1 is continuous, as is its composition with a genuinely continuous trajectory map. |
| 5.4 | `thm_5_4`: holds from 1.1 under continuity of the observable. `arbitrary_map_counterexample` refutes the unrestricted map statement. Continuity of a projection alone does not establish continuity of a propagator. |
| 5.5 | `thm_5_5`: same reduction with an explicit continuity assumption, with antipodal rather than merely coincident inputs. |
| 5.6 | `thm_5_6_continuous_kernel`: conditional repair for a continuous fixed-endpoint kernel, including paths through a prescribed intermediate point. `equal_length_unequal_action` checks a failure of the equal-length inference. Actual Feynman path integral continuity/existence is not established. |
| 6.2 | `thm_6_2`: proof from 1.1 for the continuous contour observable. One must justify continuity of the complete parameter-to-integral map. |
| 6.3 | `cor_6_3`: dimension-two specialization of 3.5, under its hypotheses. |
| 6.5 | General complex integral bisection is invalid without extra structure; `complex_bisection_counterexample`, `unit_circle_contour_no_equal_split` and `real_bisection` supply exact counterexamples and a valid scalar substitute. A theorem specific to Woodhouse contours needs explicit new assumptions. |

The sampled arc model uses a countable subset of the unit interval containing 0
and 1, together with the continuous underlying path. This is an explicit
interpretation of the article's discrete paths. Countability by itself does not
imply that a sampling set is isolated; repeated values are allowed in a loop.
The paper's statement about simple connectedness and paths without self-loops is
not a standard definition of simple connectedness. In this package, the relevant
existence claims use path-connectedness, and no false equivalence is asserted.

## Numerical audit

Arb provides rigorous bounds for specified finite numbers, not proofs of universal
topological statements and not certificates for undefined infinite-dimensional
path integrals. The paper gives no fully specified numerical Feynman or Woodhouse
kernel to evaluate across the whole sphere. The numerical test cases therefore
target concrete inferences in §§5.6 and 6.5 and are not claimed to be experimental
measurements or a certification of the full physical models.

1. For a free particle, equal spatial lengths L=1 traversed over T=1 and T=2
   have actions S=mL²/(2T), with m=1, giving S₁=1/2 and S₂=1/4. With ℏ=1 the
   respective phase factors differ. This challenges the proof's inference from
   equal lengths alone; the phase factors are not the full propagator and this
   is not a counterexample to every possible existence theorem about K.
2. Take a unit-circle arc from 1 to i and the contour differential f(z)dz/z
   with f(z)=z, so it is dz. Putting q=exp(iπ/4) splits the length equally, but
   the difference of subarc integrals after normalization by 2π is
   (2q−1−i)/(2π). Both coordinates are strictly positive. In fact, equality
   would require q=(1+i)/2, which is not on the unit circle. This is a
   counterexample to general complex contour subarc bisection, not an assertion
   about a specially constrained Woodhouse observable.

`arb_certificate.json` records 14 checks at 3,600,000 working bits, with
3,400,000 required relative bits. Every nonzero ball excludes zero and the
positive quantities are tested by Arb's strict interval comparison. Minimum
reported relative accuracy: 3,599,994 bits. The full dyadic midpoints and radii
are stored in `arb_balls.json`, with an integrity SHA-256 in the summary. The
short decimal renderings in the summary are only for readability.

## Reproduction

Lean 4.19.0, Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

```sh
lake update
lake exe cache get Mathlib/Analysis/InnerProductSpace/PiL2.lean Mathlib/Analysis/NormedSpace/Connected.lean Mathlib/Analysis/NormedSpace/BallAction.lean Mathlib/Topology/MetricSpace/HausdorffDistance.lean Mathlib/Topology/Order/IntermediateValue.lean Mathlib/SetTheory/Cardinal/Order.lean Mathlib/Tactic/Linarith.lean Mathlib/Tactic/NormNum.lean
lake build
```

FLINT 3.6.0 through python-flint 0.9.0:

```sh
python -m pip install python-flint==0.9.0
python verify_balls.py
python certify.py --balls arb_balls.recomputed.json > arb_certificate.recomputed.json
```

The last command performs the original computations afresh. The verification
script checks the archived bounds without replacing them and uses outward
rounding when restoring the radius.

The next mathematical priority is a classical proof of 1.1 in Lean 4 (e.g.,
via degree theory or a combinatorial Tucker lemma), followed by rigorous
analytic definitions and continuity theorems for the physical observables.
