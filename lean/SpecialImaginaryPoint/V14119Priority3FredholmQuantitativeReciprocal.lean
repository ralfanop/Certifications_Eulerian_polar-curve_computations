import SpecialImaginaryPoint.V14119Priority3QuantitativeFredholmNonvanishing

/-!
# Priority 3 — quantitative genuine universal Fredholm reciprocal bounds

For the actual infinite-dimensional CFC Schatten-S₁ Hilbert-compression
Fredholm determinant f_T(z)=det_F(I+zT), the independently certified
global perturbation estimate gives a LOWER bound on |f_T(z)| as well as
a sufficient criterion for nonvanishing.

If a(z,T)=‖z‖‖T‖ exp(‖z‖‖T‖)<1, then
  |f_T(z)| ≥ 1-a(z,T) > 0
and, rigorously for the actual determinant reciprocal,
  |1/f_T(z)| ≤ 1/(1-a(z,T)).

These inequalities are valid for arbitrary complex trace-class Hilbert
operators, including nonnormal and nonselfadjoint T. They concern the
scalar Fredholm reciprocal, not the norm of an inverse operator.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmQuantitativeReciprocal

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmSpectralVariation

/-- Exact quantitative lower modulus estimate of the ACTUAL
universal Fredholm determinant in terms of the true trace norm. -/
theorem universalFredholm_modulus_lower_bound
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    1 - (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) ≤
      ‖fredholmDet T z‖ := by
  have h := universalFredholm_spectral_origin_norm_le T z
  have htri : (1 : ℝ) ≤
      ‖fredholmDet T z - 1‖ + ‖fredholmDet T z‖ := by
    calc
      (1 : ℝ) = ‖(fredholmDet T z - 1) - fredholmDet T z‖ := by
        simp
      _ ≤ ‖fredholmDet T z - 1‖ + ‖fredholmDet T z‖ :=
        norm_sub_le _ _
  linarith

/-- The genuine Fredholm reciprocal has a fully explicit modulus
upper bound in the zero-exclusion region. The denominator is
strictly positive by hypothesis, so no zero-divisor artifact occurs. -/
theorem universalFredholm_reciprocal_norm_bound
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall :
      (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) < 1) :
    ‖(fredholmDet T z)⁻¹‖ ≤
      1 / (1 - (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖)) := by
  have hdenpos :
      0 < 1 - (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
    linarith
  have hden :=
    universalFredholm_modulus_lower_bound T z
  calc
    ‖(fredholmDet T z)⁻¹‖ = 1 / ‖fredholmDet T z‖ := by
      simp only [norm_inv, one_div]
    _ ≤ 1 / (1 - (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖)) :=
      one_div_le_one_div_of_le hdenpos hden

#print axioms Manuscript14Priority3.FredholmQuantitativeReciprocal.universalFredholm_modulus_lower_bound
#print axioms Manuscript14Priority3.FredholmQuantitativeReciprocal.universalFredholm_reciprocal_norm_bound

end Manuscript14Priority3.FredholmQuantitativeReciprocal
