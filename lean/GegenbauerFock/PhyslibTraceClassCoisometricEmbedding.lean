import GegenbauerFock.PhyslibTraceClassCoisometricConjugation
import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# V007 — coisometric CFC trace-class conjugation as an isometric embedding

If the bounded Hilbert-space operator U satisfies U*U† = 1,
the conjugation T ↦ U† T U has a left inverse on the genuine
CFC-trace-normed Schatten class S₁. Consequently it is injective.

If also ‖U‖ ≤ 1, that conjugation preserves the *exact* trace
norm and the induced metric, even for nonpositive, nonnormal
or nonselfadjoint trace-class inputs.

These statements do not identify source and target Fock spaces,
and do not claim surjectivity of the embedding.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Conjugation by a coisometry is injective on the actual CFC
trace-class carrier. In infinite dimension it need not be onto. -/
theorem coisometric_conjugate_injective_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    Function.Injective (fun T : TraceClass H => conjugate T U) := by
  intro T V h
  calc
    T = conjugate (conjugate T U) U.adjoint :=
      (coisometric_conjugate_inverse_v007 T U hUUstar).symm
    _ = conjugate (conjugate V U) U.adjoint :=
      congrArg (fun X : TraceClass H => conjugate X U.adjoint) h
    _ = V := coisometric_conjugate_inverse_v007 V U hUUstar

/-- Coisometric conjugation exactly preserves the genuine CFC
trace-norm distance, including for non-selfadjoint inputs. -/
theorem coisometric_conjugate_dist_eq_v007
    (U : H →L[ℂ] H)
    (hUUstar : U * U.adjoint = 1)
    (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (T V : TraceClass H) :
    dist (conjugate T U) (conjugate V U) = dist T V := by
  have hsub :
      conjugate T U - conjugate V U = conjugate (T - V) U := by
    change sandwichContinuous U.adjoint U T -
        sandwichContinuous U.adjoint U V =
      sandwichContinuous U.adjoint U (T - V)
    exact (map_sub (sandwichContinuous U.adjoint U) T V).symm
  calc
    dist (conjugate T U) (conjugate V U) =
        traceNorm H (conjugate T U - conjugate V U) := by
      rw [dist_eq_norm, norm_eq_genuineTraceNorm]
    _ = traceNorm H (conjugate (T - V) U) := by rw [hsub]
    _ = traceNorm H (T - V) :=
      coisometric_conjugate_traceNorm_eq_v007 (T - V) U hUUstar hUnorm
    _ = dist T V := by rw [dist_eq_norm, norm_eq_genuineTraceNorm]

#print axioms ProbabilisticTheory.TraceClass.coisometric_conjugate_injective_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_conjugate_dist_eq_v007

end ProbabilisticTheory.TraceClass
