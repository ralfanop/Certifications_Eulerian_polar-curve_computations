import GegenbauerFock.PhyslibTraceClassSubmultiplicative

/-!
# V007 — positive powers in the genuine CFC trace-class algebra

The identity need not be trace class on an infinite-dimensional Hilbert
space, so we deliberately index only *positive* powers T^(n+1).
The real trace norm is the already certified CFC absolute-operator norm.

For every trace-class T and natural n:
  T^(n+1) ∈ S₁(H), ‖T^(n+1)‖₁ ≤ ‖T‖₁^(n+1).

We do not use or claim a unit in S₁, do not postulate an abstract
Banach-algebra instance, and impose no finite-dimensional restrictions.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strictly positive powers, defined entirely within the actual
proof-carrying trace-class carrier. -/
noncomputable def positivePower (T : TraceClass H) : ℕ → TraceClass H
  | 0 => T
  | n + 1 => product (positivePower T n) T

@[simp] theorem positivePower_zero (T : TraceClass H) :
    positivePower T 0 = T := rfl

@[simp] theorem positivePower_succ (T : TraceClass H) (n : ℕ) :
    positivePower T (n + 1) = product (positivePower T n) T := rfl

/-- The underlying operator is exactly its ordinary positive power
in the full bounded-operator algebra. -/
theorem positivePower_operator (T : TraceClass H) (n : ℕ) :
    (positivePower T n).1 = T.1 ^ (n + 1) := by
  induction n with
  | zero =>
      simp only [positivePower_zero, zero_add, pow_one]
  | succ n ih =>
      change (positivePower T n).1 * T.1 = T.1 ^ (n + 1 + 1)
      rw [ih, pow_succ]

/-- Sharp coefficient-one submultiplicative estimate on every
strictly positive CFC Schatten-S₁ power. -/
theorem norm_positivePower_le (T : TraceClass H) (n : ℕ) :
    ‖positivePower T n‖ ≤ ‖T‖ ^ (n + 1) := by
  induction n with
  | zero =>
      simp only [positivePower_zero, zero_add, pow_one, le_refl]
  | succ n ih =>
      calc
        ‖positivePower T (n + 1)‖ ≤
            ‖positivePower T n‖ * ‖T‖ := by
          change ‖product (positivePower T n) T‖ ≤ _
          exact norm_product_le _ _
        _ ≤ ‖T‖ ^ (n + 1) * ‖T‖ :=
          mul_le_mul_of_nonneg_right ih (norm_nonneg _)
        _ = ‖T‖ ^ (n + 1 + 1) := by rw [pow_succ]

#print axioms ProbabilisticTheory.TraceClass.positivePower_operator
#print axioms ProbabilisticTheory.TraceClass.norm_positivePower_le

end ProbabilisticTheory.TraceClass
