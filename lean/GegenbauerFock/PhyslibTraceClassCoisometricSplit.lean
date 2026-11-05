import GegenbauerFock.PhyslibTraceClassSandwichComposition

/-!
# V007 — split continuous Schatten S₁ coisometric conjugation

For a bounded coisometry U on a complete complex Hilbert space
(U * U† = 1), two genuine CFC trace-class endomorphisms admit an
exact splitting:

  (T ↦ U T U†) ∘ (T ↦ U† T U) = identity on S₁.

This expresses a split injection and a split surjection in the
category of *continuous complex-linear* operators, not just
an algebraic or operator-norm identity. It does not claim that
conjugation T ↦ U†TU is surjective in infinite dimension.

No norm-one hypothesis, positivity, or trace-class identity
is required for this split; the separate exact trace-norm
isometry can add metric information.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The bounded CFC trace-class sandwich maps give an exact left
inverse for conjugation by any coisometry. -/
theorem coisometric_sandwich_split_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    (sandwichContinuous U U.adjoint).comp
        (sandwichContinuous U.adjoint U) =
      ContinuousLinearMap.id ℂ (TraceClass H) := by
  rw [sandwichContinuous_comp, hUUstar,
    sandwichContinuous_one_one_eq_id]

/-- Pointwise form of the exact continuous split identity. -/
theorem coisometric_sandwich_split_apply_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T : TraceClass H) :
    sandwichContinuous U U.adjoint
        (sandwichContinuous U.adjoint U T) = T := by
  have h := congrArg
    (fun f : TraceClass H →L[ℂ] TraceClass H => f T)
    (coisometric_sandwich_split_v007 U hUUstar)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply] using h

/-- The split inner coisometric conjugation is injective as a map
on the genuine CFC Schatten S₁ class, independently of positivity. -/
theorem coisometric_sandwich_injective_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    Function.Injective (sandwichContinuous U.adjoint U) := by
  intro T V hEq
  calc
    T = sandwichContinuous U U.adjoint
        (sandwichContinuous U.adjoint U T) :=
      (coisometric_sandwich_split_apply_v007 U hUUstar T).symm
    _ = sandwichContinuous U U.adjoint
        (sandwichContinuous U.adjoint U V) := by rw [hEq]
    _ = V := coisometric_sandwich_split_apply_v007 U hUUstar V

/-- The companion coisometric sandwich T ↦ U T U† is surjective:
it admits the explicit S₁-valued right inverse T ↦ U† T U. -/
theorem coisometric_sandwich_surjective_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    Function.Surjective (sandwichContinuous U U.adjoint) := by
  intro T
  exact ⟨sandwichContinuous U.adjoint U T,
    coisometric_sandwich_split_apply_v007 U hUUstar T⟩

#print axioms ProbabilisticTheory.TraceClass.coisometric_sandwich_split_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_sandwich_split_apply_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_sandwich_injective_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_sandwich_surjective_v007

end ProbabilisticTheory.TraceClass
