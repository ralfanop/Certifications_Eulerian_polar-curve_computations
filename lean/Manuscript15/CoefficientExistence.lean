import Manuscript15.CoefficientRigidity
import Mathlib

/-!
# Manuscript 15 — exact existence and uniqueness of the full rigidity coefficient sequence

The previously certified conditional CoefficientRule gives a triangular
quadratic recurrence. Every coefficient of index n+1 is determined by
the first n+1 coefficients, divided by the strictly positive factor
(2n+3) 4^(n+1).

This module constructs a REAL sequence at ALL natural-number indices
using Mathlib's well-founded strong recursion, then proves it satisfies
the exact recurrence with c₀=1. Together with the previously certified
CoefficientRule uniqueness theorem, this yields unconditional
EXISTENCE AND UNIQUENESS OF AN ALGEBRAIC SEQUENCE satisfying the rule.

This is not yet existence of an entire analytic characteristic function
realizing those coefficients or existence of a probability measure;
such analytic and probabilistic realization remains a separate task.
-/

noncomputable section

namespace Manuscript15

/-- Canonical exact algebraic coefficient sequence produced by the
two-scale quadratic recurrence through strong well-founded recursion. -/
noncomputable def rigidityCoefficientSequence (n : ℕ) : ℝ :=
  Nat.strongRecOn n (fun n ih =>
    match n with
    | 0 => 1
    | k + 1 =>
        -((1 / 2 : ℝ) *
          ∑ j ∈ Finset.range (k + 1),
            ih j (by omega) * ih (k - j) (by omega)) /
          ((((2 * (k + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (k + 1))))

/-- The exact base coefficient of the canonical sequence. -/
theorem rigidityCoefficientSequence_zero :
    rigidityCoefficientSequence 0 = 1 := by
  unfold rigidityCoefficientSequence
  rw [Nat.strongRecOn_eq]

/-- The exact recursion equation, without any floating-point
arithmetic or manual assignment of finitely many coefficients. -/
theorem rigidityCoefficientSequence_succ (n : ℕ) :
    rigidityCoefficientSequence (n + 1) =
      -((1 / 2 : ℝ) *
        ∑ j ∈ Finset.range (n + 1),
          rigidityCoefficientSequence j *
            rigidityCoefficientSequence (n - j)) /
        ((((2 * (n + 1) + 1 : ℕ) : ℝ) * (4 : ℝ) ^ (n + 1))) := by
  conv_lhs =>
    rw [rigidityCoefficientSequence, Nat.strongRecOn_eq]
  rfl

/-- The exact infinite coefficient sequence satisfies the full
Manuscript 15 two-scale rigidity recurrence, for ALL n. -/
theorem rigidityCoefficientSequence_rule :
    CoefficientRule rigidityCoefficientSequence := by
  constructor
  · exact rigidityCoefficientSequence_zero
  · intro n
    have hD :
        ((((2 * (n + 1) + 1 : ℕ) : ℝ) *
            (4 : ℝ) ^ (n + 1))) ≠ 0 := by positivity
    rw [rigidityCoefficientSequence_succ n]
    field_simp [hD]

/-- There exists an exact real-valued sequence satisfying the full
two-scale algebraic coefficient recurrence and c₀=1. -/
theorem coefficientRule_exists :
    ∃ c : ℕ → ℝ, CoefficientRule c :=
  ⟨rigidityCoefficientSequence, rigidityCoefficientSequence_rule⟩

/-- Every solution of the exact two-scale rigidity recurrence agrees
pointwise with the canonical well-founded coefficient sequence. -/
theorem coefficientRule_eq_canonical
    (c : ℕ → ℝ) (hc : CoefficientRule c) :
    c = rigidityCoefficientSequence :=
  coefficientRule_unique c rigidityCoefficientSequence
    hc rigidityCoefficientSequence_rule

/-- Existence and uniqueness of the EXACT formal algebraic recurrence
sequence; no analytic convergence or probability-measure claim. -/
theorem coefficientRule_existsUnique :
    ∃! c : ℕ → ℝ, CoefficientRule c := by
  refine ⟨rigidityCoefficientSequence, rigidityCoefficientSequence_rule, ?_⟩
  intro c hc
  exact coefficientRule_eq_canonical c hc

#print axioms Manuscript15.rigidityCoefficientSequence_zero
#print axioms Manuscript15.rigidityCoefficientSequence_succ
#print axioms Manuscript15.rigidityCoefficientSequence_rule
#print axioms Manuscript15.coefficientRule_exists
#print axioms Manuscript15.coefficientRule_eq_canonical
#print axioms Manuscript15.coefficientRule_existsUnique

end Manuscript15
