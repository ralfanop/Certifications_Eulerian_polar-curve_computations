import GegenbauerFock.UltrasphericalPolynomialL2
import GegenbauerFock.UltrasphericalContinuousDensity

/-!
# V007 — quantitative genuine ultraspherical polynomial L² approximation

Once a complex polynomial P is uniformly close on the *true compact
support* [-1,1] to a bounded complex continuous function f, the
actual element of L²(ν_λ) representing P is close to the image of f.
Crucially, the polynomial L² element is one of the *original Riesz
monomial span* elements.

The existence of sufficiently good complex polynomials for every f
(Stone–Weierstrass real/imaginary combination) remains the final
separate density obligation; it is not smuggled in as an assumption.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Ordinary complex polynomial evaluation is continuous on the
entire real line (despite potentially being unbounded there). -/
theorem sourcePolynomial_eval_continuous (P : Polynomial ℂ) :
    Continuous (fun u : ℝ => P.eval (u : ℂ)) := by
  fun_prop

/-- Uniform approximation of a bounded continuous complex function
by a complex polynomial on [-1,1] controls the *true L²(ν_λ) distance*
to the weighted Riesz-monomial combination associated with P. -/
theorem boundedContinuous_sourcePolynomial_norm_sub_le
    (lam : ℝ) (hlam : 0 < lam)
    (f : BoundedContinuousFunction ℝ ℂ) (P : Polynomial ℂ)
    (eps : ℝ) (heps : 0 ≤ eps)
    (huniform : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      ‖f u - P.eval (u : ℂ)‖ ≤ eps) :
    ‖Ultraspherical.boundedContinuousToLp lam hlam f -
        sourcePolynomial lam hlam P‖ ≤ eps := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  have hbound := Ultraspherical.eLpNorm_sub_le_of_uniform_error_unit_interval
    lam hlam (fun u => f u) (fun u => P.eval (u : ℂ))
    f.continuous (sourcePolynomial_eval_continuous P) eps huniform
  have hf :
      ((Ultraspherical.boundedContinuousToLp lam hlam f :
          Lp ℂ 2 (Ultraspherical.measure lam)) : ℝ → ℂ)
        =ᵐ[Ultraspherical.measure lam] (f : ℝ → ℂ) := by
    change
      ((BoundedContinuousFunction.toLp
        (2 : ℝ≥0∞) (Ultraspherical.measure lam) ℂ f :
            Lp ℂ 2 (Ultraspherical.measure lam)) : ℝ → ℂ)
        =ᵐ[Ultraspherical.measure lam] (f : ℝ → ℂ)
    exact BoundedContinuousFunction.coeFn_toLp
      (2 : ℝ≥0∞) (Ultraspherical.measure lam) ℂ f
  have hdifference :
      ((Ultraspherical.boundedContinuousToLp lam hlam f -
        sourcePolynomial lam hlam P :
          Lp ℂ 2 (Ultraspherical.measure lam)) : ℝ → ℂ)
      =ᵐ[Ultraspherical.measure lam]
        (fun u => f u - P.eval (u : ℂ)) := by
    filter_upwards
      [Lp.coeFn_sub
        (Ultraspherical.boundedContinuousToLp lam hlam f)
        (sourcePolynomial lam hlam P),
       hf, sourcePolynomial_ae_eval lam hlam P]
      with u hsub hfu hpoly
    simpa only [Pi.sub_apply, hfu, hpoly] using hsub
  rw [Lp.norm_def, eLpNorm_congr_ae hdifference]
  exact ENNReal.toReal_le_of_le_ofReal heps hbound

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourcePolynomial_eval_continuous
#print axioms GegenbauerFock.GeneralUltrasphericalFock.boundedContinuous_sourcePolynomial_norm_sub_le

end GegenbauerFock.GeneralUltrasphericalFock
