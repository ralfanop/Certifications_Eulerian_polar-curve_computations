import GegenbauerFock.AnalyticAdjointComplete

/-!
# V007: exact L² integral Gram operator, not a merely formal kernel

The integral-kernel operator is first defined as a genuine bounded
continuous linear map via analytic Fock restriction composed with C,
with every value explicitly identified as the Bochner exponential
kernel integral in L². The analytic-adjoint theorem then identifies
this independently constructed integral operator with C†C.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Genuine bounded real-exponential integral operator, constructed
as the analytic restriction of the entire Gegenbauer–Fock transform. -/
noncomputable def gramIntegralOperator
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  (FockAnalyticRestriction.restrictionCLM lam alpha hlam ha).comp
    (C lam alpha hlam ha)

/-- Every value of the genuine bounded integral operator is exactly
the L² class of the Bochner integral u↦∫e^(uv/(4α))f(v)dνλ(v). -/
theorem gramIntegralOperator_apply
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    gramIntegralOperator lam alpha hlam ha f =
      gramKernelIntegralLp lam alpha hlam ha f := by
  change FockAnalyticRestriction.restrictionLp lam alpha hlam ha
    (C lam alpha hlam ha f) = _
  exact (gramKernelIntegralLp_eq_restriction lam alpha hlam ha f).symm

/-- Full operator identity: the existing concrete Hilbert Gram
C†C is the actual bounded Bochner integral-kernel operator. -/
theorem gram_eq_gramIntegralOperator
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    gram lam alpha hlam ha =
      gramIntegralOperator lam alpha hlam ha := by
  unfold gram gramIntegralOperator
  rw [FockAnalyticRestriction.restrictionCLM_eq_C_adjoint
    lam alpha hlam ha]
  rfl

/-- Final pointwise-in-L² equality for arbitrary L² inputs:
the Gram C†C is the genuine exponential Bochner kernel integral. -/
theorem gram_eq_integralLp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    gram lam alpha hlam ha f =
      gramKernelIntegralLp lam alpha hlam ha f := by
  rw [gram_eq_gramIntegralOperator]
  exact gramIntegralOperator_apply lam alpha hlam ha f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_apply
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_eq_gramIntegralOperator
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_eq_integralLp

end GegenbauerFock.GeneralUltrasphericalFock
