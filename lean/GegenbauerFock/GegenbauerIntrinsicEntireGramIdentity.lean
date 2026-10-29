import GegenbauerFock.GegenbauerIntrinsicEntireGramPairing
import GegenbauerFock.GramIntegralComplete

/-!
# V007 — equality of the genuine intrinsic entire Fock Gram and Bochner kernel

The onto Gaussian Bargmann–Fock coefficient synthesis is an isometric
equivalence with the independently defined intrinsic entire Gaussian L²
Hilbert space. Thus the source Gram of the true holomorphic realization
coincides *as a continuous linear operator*, not merely as a sesquilinear
form, with the source Gram of the ultraspherical coefficient transform.
The latter has already been identified with its genuine L² Bochner
exponential-kernel integral.

This module makes no assertion that the compact ultraspherical transform
is onto: it is injective with proper dense nonclosed range.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The source Gram of the ultraspherical transform into the genuine
intrinsic entire Gaussian Fock Hilbert space is exactly the existing
coefficient-space source Gram, as an identity of bounded operators. -/
theorem C_intrinsicEntire_gram_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha) =
      gram lam alpha hlam ha := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℂ
  intro g
  exact C_intrinsicEntire_gram_pairing lam alpha hlam ha f g

/-- The genuine holomorphic Fock realization has the same bounded
source Gram as the actual exponential Bochner integral operator. -/
theorem C_intrinsicEntire_gram_eq_integralOperator
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha) =
      gramIntegralOperator lam alpha hlam ha := by
  rw [C_intrinsicEntire_gram_eq, gram_eq_gramIntegralOperator]

/-- Explicit L² equality at every input: the genuine intrinsic Fock
source Gram equals the integral-kernel class with exp(uv/(4α)). -/
theorem C_intrinsicEntire_gram_eq_integralLp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    HilbertGram.gram (C_intrinsicEntire lam alpha hlam ha) f =
      gramKernelIntegralLp lam alpha hlam ha f := by
  rw [C_intrinsicEntire_gram_eq]
  exact gram_eq_integralLp lam alpha hlam ha f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eq_integralOperator
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eq_integralLp

end GegenbauerFock.GeneralUltrasphericalFock
