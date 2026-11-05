import GegenbauerFock.GegenbauerIntrinsicEntireGramPairing
import GegenbauerFock.GramIntegralComplete

/-!
# V007 — equality of the intrinsic entire Fock Gram and Bochner kernel

The fully analytic Gaussian Fock codomain is closed, hence complete.
Its true source Gram is built with the local Hilbert completeness
instance, transported along the certified Gaussian coefficient
isometry, and identified with the Bochner exponential integral.
No surjectivity of the compact Gegenbauer transform is assumed.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine intrinsic entire Gaussian Fock source Gram coincides
with the coefficient-space source Gram as a bounded operator identity. -/
theorem C_intrinsicEntire_gram_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    C_intrinsicEntire_gram lam alpha hlam ha =
      gram lam alpha hlam ha := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  exact C_intrinsicEntire_gram_pairing lam alpha hlam ha f g

/-- The intrinsic Gaussian Fock Gram equals the actual bounded
real-exponential Bochner-kernel integral operator on ultraspherical L². -/
theorem C_intrinsicEntire_gram_eq_integralOperator
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    C_intrinsicEntire_gram lam alpha hlam ha =
      gramIntegralOperator lam alpha hlam ha := by
  rw [C_intrinsicEntire_gram_eq, gram_eq_gramIntegralOperator]

/-- Genuine L² kernel identity at every source input, with
K(u,v) = exp(uv/(4α)). -/
theorem C_intrinsicEntire_gram_eq_integralLp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    C_intrinsicEntire_gram lam alpha hlam ha f =
      gramKernelIntegralLp lam alpha hlam ha f := by
  rw [C_intrinsicEntire_gram_eq]
  exact gram_eq_integralLp lam alpha hlam ha f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eq_integralOperator
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eq_integralLp

end GegenbauerFock.GeneralUltrasphericalFock
