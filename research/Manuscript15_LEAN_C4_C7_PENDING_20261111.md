# Manuscript 15 — Lean c4–c7 extension (status: candidate)

Source version: Manuscript15_Revision_20261111d, 11 November 2026.

This independent draft extends `lean/Manuscript15/CoefficientRigidity.lean`, building on the kernel-checked `CoefficientRule` and `coefficientRule_c_one`–`coefficientRule_c_three` results.

Under the existing **conditional** hypothesis `CoefficientRule c`, new Lean declarations assert exactly:
- `c 4 = 1/92897280`
- `c 5 = -1/40874803200`
- `c 6 = 1/25505877196800`
- `c 7 = -1/21424936845312000`

Each rational value has also been independently recomputed with Python `fractions.Fraction` (exact integer/rational arithmetic, not Arb). Matching rational values do not by themselves establish the Lean proofs.

**Acceptance requirement:** the pinned GitHub Actions check must complete successfully on the exact commit head; the CI prints `#print axioms` for all seven coefficient theorems, rejects `sorryAx` and `Lean.ofReduceBool`, and preserves the previous uniqueness proof. Do not count the four new declarations as kernel-certified before that run.

**Scope limitation:** these are consequences *of the recurrence*. Deriving `CoefficientRule` from the characteristic function of a compactly supported symmetric probability measure, the uniqueness of that measure, and all remaining manuscript theorems are separate formalisation obligations.

No changes to Manuscripts 11–14, V007 or V097. This proposal is independent from the 10000-bit Arb PR #179 and must not be merged until its own CI succeeds.
