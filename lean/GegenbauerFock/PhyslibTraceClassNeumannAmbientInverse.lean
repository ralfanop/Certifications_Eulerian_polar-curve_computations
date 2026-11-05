import GegenbauerFock.PhyslibTraceClassNeumannQuasiregular

/-!
# V007 — the nonunital Schatten Neumann correction in the unital ambient algebra

The trace class is a complete nonunital algebra, but its ambient algebra
of bounded complex-linear endomorphisms has a unit.  For a trace-class
operator T with ‖T‖₁ < 1, let S be the nonunital sum of iterated products
T + T² + ⋯.  The two Neumann identities inside S₁ give an explicit
two-sided inverse of (1 - T.1) in the ambient operator algebra:

  (1 - T.1) * (1 + S.1) = 1 = (1 + S.1) * (1 - T.1).

In particular, the ambient bounded operator (1 - T.1) is a unit.
We never assert that the identity bounded operator belongs to S₁.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The nonunital Neumann correction as a genuine trace-class element. -/
noncomputable def neumannCorrection (T : TraceClass H) : TraceClass H :=
  ∑' n : ℕ, (· * T)^[n] T

/-- Explicit left and right inverse identities in the ambient
unital Banach algebra of bounded complex-linear maps. -/
theorem neumann_ambient_two_sided_inverse
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    (((1 : H →L[ℂ] H) - T.1) * (1 + (neumannCorrection T).1) = 1) ∧
    (((1 : H →L[ℂ] H) + (neumannCorrection T).1) * (1 - T.1) = 1) := by
  let S : TraceClass H := neumannCorrection T
  have hS := neumann_two_sided_identities T hsmall
  have hr := congrArg (fun X : TraceClass H => X.1) hS.2
  have hl := congrArg (fun X : TraceClass H => X.1) hS.1
  change T.1 + T.1 * S.1 = S.1 at hr
  change T.1 + S.1 * T.1 = S.1 at hl
  constructor
  · calc
      ((1 : H →L[ℂ] H) - T.1) * (1 + S.1) =
          (1 + S.1) - (T.1 + T.1 * S.1) := by
            rw [sub_mul, one_mul, mul_add, mul_one]
      _ = 1 := by rw [hr]; exact add_sub_cancel_right _ _
  · calc
      ((1 : H →L[ℂ] H) + S.1) * (1 - T.1) =
          (1 + S.1) - (T.1 + S.1 * T.1) := by
            rw [mul_sub, mul_one, add_mul, one_mul]
      _ = 1 := by rw [hl]; exact add_sub_cancel_right _ _

/-- Trace-norm contraction gives invertibility of 1 - T in the
ambient operator algebra, with a concrete trace-class correction. -/
theorem neumann_ambient_one_sub_isUnit
    (T : TraceClass H) (hsmall : ‖T‖ < 1) :
    IsUnit ((1 : H →L[ℂ] H) - T.1) := by
  exact isUnit_iff_exists.mpr
    ⟨(1 : H →L[ℂ] H) + (neumannCorrection T).1,
      (neumann_ambient_two_sided_inverse T hsmall).1,
      (neumann_ambient_two_sided_inverse T hsmall).2⟩

#print axioms ProbabilisticTheory.TraceClass.neumann_ambient_two_sided_inverse
#print axioms ProbabilisticTheory.TraceClass.neumann_ambient_one_sub_isUnit

end ProbabilisticTheory.TraceClass
