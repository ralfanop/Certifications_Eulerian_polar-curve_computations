import GegenbauerFock.FockAnalyticRestriction

/-!
# V007: the exponential Gram kernel produces an actual ultraspherical L² class

No abstract integral operator is smuggled into the construction. The
pointwise Bochner integral was identified with analytic Fock evaluation,
whose general L² membership is separately established. This certifies
the genuine kernel integral as an L²-valued function for each input,
but does NOT by itself identify it with the adjoint-Gram operator.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For every f∈L²(νλ), the explicit exponential-kernel integral is
a genuine member of L²(νλ), not merely a formal pointwise expression. -/
theorem gramKernelIntegral_memLp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    MemLp (gramKernelIntegral lam alpha f)
      2 (Ultraspherical.measure lam) := by
  have heq :
      gramKernelIntegral lam alpha f =
        FockAnalyticRestriction.evaluate alpha ha (C lam alpha hlam ha f) := by
    funext u
    exact (evaluation_imaginary_eq_gramKernelIntegral
      lam alpha hlam ha f u).symm
  rw [heq]
  exact FockAnalyticRestriction.memLp_evaluate
    lam alpha hlam ha (C lam alpha hlam ha f)

/-- Actual L² class constructed from the explicit integral
u ↦ ∫ exp(u*v/(4α)) f(v) dνλ(v). -/
noncomputable def gramKernelIntegralLp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    Lp ℂ 2 (Ultraspherical.measure lam) :=
  (gramKernelIntegral_memLp lam alpha hlam ha f).toLp
    (gramKernelIntegral lam alpha f)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegral_memLp

/-- The true exponential-kernel Bochner integral and the
imaginary-axis analytic Fock restriction determine the *same*
L² equivalence class, not just pointwise scalar values. -/
theorem gramKernelIntegralLp_eq_restriction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    gramKernelIntegralLp lam alpha hlam ha f =
      FockAnalyticRestriction.restrictionLp lam alpha hlam ha
        (C lam alpha hlam ha f) := by
  have hfun :
      gramKernelIntegral lam alpha f =
        FockAnalyticRestriction.evaluate alpha ha
          (C lam alpha hlam ha f) := by
    funext u
    exact (evaluation_imaginary_eq_gramKernelIntegral
      lam alpha hlam ha f u).symm
  unfold gramKernelIntegralLp FockAnalyticRestriction.restrictionLp
  rw [hfun]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramKernelIntegralLp_eq_restriction


end GegenbauerFock.GeneralUltrasphericalFock
