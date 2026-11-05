import GegenbauerFock.GramKernelSeries

/-!
# V007: the exact exponential integral on the imaginary Fock segment

For every positive λ and α, and every L² input, the actual Fock
evaluation of C at w=-i*u/(2α) equals an actual Bochner integral with
real positive Gram kernel exp(u*v/(4α)).
The separate remaining identification of this pointwise function
with an L² representative of C†C requires the full analytic adjoint
restriction theorem. No such identification is assumed here.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The authentic complex scalar integral with the real symmetric
positive exponential kernel, defined for all real evaluation points. -/
noncomputable def gramKernelIntegral (lam alpha : ℝ)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (u : ℝ) : ℂ :=
  ∫ v : ℝ, f v * (Real.exp (u * v / (4 * alpha)) : ℂ)
    ∂(Ultraspherical.measure lam)

/-- Evaluating the actual Fock transform on the imaginary segment
is exactly the weighted exponential Bochner integral, pointwise in u.
No unproved interchange or pointwise interpretation of an L² class
occurs in this statement. -/
theorem evaluation_imaginary_eq_gramKernelIntegral
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (u : ℝ) :
    FockEvaluation.evaluation alpha ha
      (-Complex.I * (u : ℂ) / (2 * (alpha : ℂ)))
      (C lam alpha hlam ha f) =
      gramKernelIntegral lam alpha f u := by
  change evaluatedOperator lam alpha hlam ha
    (-Complex.I * (u : ℂ) / (2 * (alpha : ℂ))) f = _
  rw [evaluatedOperator_eq_integral]
  unfold gramKernelIntegral
  apply integral_congr_ae
  filter_upwards [] with v
  have haC : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt ha)
  have harg :
      Complex.I *
        (-Complex.I * (u : ℂ) / (2 * (alpha : ℂ))) *
          (v : ℂ) / 2 =
        ((u * v / (4 * alpha) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring_nf
    simp [Complex.I_mul_I]
  rw [harg, ← Complex.ofReal_exp]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluation_imaginary_eq_gramKernelIntegral

end GegenbauerFock.GeneralUltrasphericalFock
