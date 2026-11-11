# Manuscript 15 — Lean c4–c7 extension (status: exact-source kernel-certified)

Source version: Manuscript15_Revision_20261111d, 11 November 2026.

This independent draft extends `lean/Manuscript15/CoefficientRigidity.lean`, building on the kernel-checked `CoefficientRule` and `coefficientRule_c_one`–`coefficientRule_c_three` results.

Under the existing **conditional** hypothesis `CoefficientRule c`, new Lean declarations assert exactly:
- `c 4 = 1/92897280`
- `c 5 = -1/40874803200`
- `c 6 = 1/25505877196800`
- `c 7 = -1/21424936845312000`

Each rational value has also been independently recomputed with Python `fractions.Fraction` (exact integer/rational arithmetic, not Arb). Matching rational values do not by themselves establish the Lean proofs.

**Kernel certification: SUCCESS.** The pinned [GitHub Actions run 43080899625](https://github.com/ralfanop/Certifications_Eulerian_polar-curve_computations/actions/runs/43080899625) completed successfully on source commit `eac61f1a35ad4c1e09985574a993244bf5268b0e`. Its Lean kernel log prints the axioms for **all seven** coefficient theorems and coefficient uniqueness. Each depended only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or `Lean.ofReduceBool` occurred. The four exact coefficients c4–c7 are **now formally certified as consequences of `CoefficientRule`**. Changing this ledger does not alter the successfully checked Lean source.

**Scope limitation:** these are consequences *of the recurrence*. Deriving `CoefficientRule` from the characteristic function of a compactly supported symmetric probability measure, the uniqueness of that measure, and all remaining manuscript theorems are separate formalisation obligations.

No changes to Manuscripts 11–14, V007 or V097. This proposal is independent from the 10000-bit Arb PR #179 and must not be merged until its own CI succeeds.
