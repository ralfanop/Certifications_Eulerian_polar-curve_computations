import GegenbauerFock.PhyslibTraceClassCommutatorContinuous
import GegenbauerFock.PhyslibTraceClassComplexNonUnitalAlgebra

/-!
# V007 — Jacobi representation of the ambient bounded-operator Lie algebra on CFC S₁

For arbitrary bounded A,B and trace-class T, the continuous inner
derivations satisfy [ad_A, ad_B](T) = ad_[A,B](T), with the operator
norm estimate ‖ad_[A,B]‖ ≤ 4 ‖A‖ ‖B‖.

The proof works on any complete complex Hilbert space (including
the zero space), and imposes no selfadjointness or trace-class
restriction on A or B. The norm is the true CFC trace norm.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Jacobi identity in the actual proof-carrying Schatten-S₁ subtype:
the commutator of inner derivations equals the derivation of
the ambient bounded-operator commutator. -/
theorem commutatorContinuous_jacobi
    (A B : H →L[ℂ] H) (T : TraceClass H) :
    commutatorContinuous A (commutatorContinuous B T) -
      commutatorContinuous B (commutatorContinuous A T) =
        commutatorContinuous (A * B - B * A) T := by
  apply Subtype.ext
  simp only [sub_operator, commutatorContinuous_operator]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- The Lie-algebra identity holds as equality of genuine bounded
complex-linear operators on the true Schatten-S₁ Banach space. -/
theorem commutatorContinuous_jacobi_operator (A B : H →L[ℂ] H) :
    (commutatorContinuous A).comp (commutatorContinuous B) -
      (commutatorContinuous B).comp (commutatorContinuous A) =
        commutatorContinuous (A * B - B * A) := by
  apply ContinuousLinearMap.ext
  intro T
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
    using commutatorContinuous_jacobi A B T

/-- Sharp universal coefficient-four estimate for the commutator
representation at two bounded ambient Hilbert operators. -/
theorem norm_commutatorContinuous_bracket_le (A B : H →L[ℂ] H) :
    ‖commutatorContinuous (A * B - B * A)‖ ≤
      4 * ‖A‖ * ‖B‖ := by
  have hAB : ‖A * B - B * A‖ ≤ 2 * ‖A‖ * ‖B‖ := by
    calc
      ‖A * B - B * A‖ ≤ ‖A * B‖ + ‖B * A‖ := norm_sub_le _ _
      _ ≤ ‖A‖ * ‖B‖ + ‖B‖ * ‖A‖ :=
        add_le_add (norm_mul_le A B) (norm_mul_le B A)
      _ = 2 * ‖A‖ * ‖B‖ := by ring
  calc
    ‖commutatorContinuous (A * B - B * A)‖ ≤
        2 * ‖A * B - B * A‖ :=
      commutatorContinuous_norm_le _
    _ ≤ 2 * (2 * ‖A‖ * ‖B‖) :=
      mul_le_mul_of_nonneg_left hAB (by norm_num)
    _ = 4 * ‖A‖ * ‖B‖ := by ring

#print axioms ProbabilisticTheory.TraceClass.commutatorContinuous_jacobi
#print axioms ProbabilisticTheory.TraceClass.commutatorContinuous_jacobi_operator
#print axioms ProbabilisticTheory.TraceClass.norm_commutatorContinuous_bracket_le

end ProbabilisticTheory.TraceClass
