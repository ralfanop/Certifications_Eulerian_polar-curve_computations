# Manuscript 15 — Compatibility and stability: Lean proof ledger

**Source version:** Manuscript15_Revision_20261111e (23 pages).
**Formalization:** `lean/Manuscript15/CycloidalReconstruction.lean` (no changes to the underlying definitions).

Nine proposed declarations:
1. `reconstruction_compatibility_polynomial`: exact division-free identity `2*a*Y a f t=(a*t-2*X a f (t/2))²`, including a=0 and t=0.
2. `reconstruction_compatibility`: manuscript compatibility identity for a≠0 (Proposition on p. 13).
3. `reconstruction_inverse`: formula recovering f(t) from X(t/2) for a*t≠0.
4. `reconstruction_first_coordinate_injective`: function injectivity given f(0)=g(0) and identical X; the measure-level uniqueness theorem remains separate.
5. `reconstruction_X_difference`: exact factorization of the X coordinate difference in absolute value.
6. `reconstruction_X_stability`: inequality `|X_f(t)-X_g(t)|≤2*|a|*t²*δ` given `∀s, |f(s)-g(s)|≤|s|*δ`.
7. `squared_difference_bound`: elementary `|u²-v²|≤2|u-v|` for `|u|,|v|≤1`.
8. `reconstruction_Y_difference`: factorization of the Y coordinate difference.
9. `reconstruction_Y_stability`: inequality `|Y_f(t)-Y_g(t)|≤|a|·|t|³·δ` under the pointwise kernel bound and `|f|,|g|≤1`.

Together the X/Y bounds recover the exact *algebraic* constants in the manuscript's W₁ theorem after instantiating `δ=W₁(μ,ν)`. Proving the characteristic-function bound from Wasserstein couplings and the unit-modulus hypothesis of a probability characteristic function remain separate formal obligations.

All assertions are **CANDIDATES** until exact-head CI succeeds with permitted kernel axioms. The workflow uses the repository's pinned Lean 4 and Mathlib and rejects `sorryAx` and `Lean.ofReduceBool`. None of the nine statements establish full W₁ coupling, analytic rigidity of probability measures, or a new result in physics.

Previous Manuscripts 11–14 and V007/V097 are unchanged. This draft has no merge authorization.
