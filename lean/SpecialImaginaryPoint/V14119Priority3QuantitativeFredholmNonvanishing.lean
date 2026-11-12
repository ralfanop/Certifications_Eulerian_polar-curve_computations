import SpecialImaginaryPoint.V14119Priority3UniversalFredholmSpectralVariation

/-!
# Priority 3 — quantitative spectral exclusion and trace-norm stability

These are theorems about the actual universal CFC-S₁ Hilbert-compression-limit
Fredholm determinant of arbitrary complex trace-class Hilbert operators.

The global spectral-parameter estimate and the genuine trace-norm
operator-perturbation estimate produce quantitative, directly usable
nonvanishing criteria. In particular a true Fredholm spectral zero
forces an explicit lower bound on its spectral parameter.

No normality, positivity, selfadjointness or eigenvalue enumeration
is assumed. No claim is made about optimal constants or a spectral
operator-invertibility criterion.
-/

noncomputable section

namespace Manuscript14Priority3.QuantitativeFredholmNonvanishing

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmSpectralVariation

/-- A fully explicit sufficient condition for the genuine universal
CFC-S₁ Fredholm determinant to be nonzero at a complex parameter. -/
theorem universalFredholm_nonzero_of_quantitative_bound
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall :
      (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) < 1) :
    fredholmDet T z ≠ 0 := by
  intro hz
  have hb := universalFredholm_spectral_origin_norm_le T z
  simp only [hz, zero_sub, norm_neg, norm_one] at hb
  exact (not_lt_of_ge hb) hsmall

/-- Every actual zero satisfies the complementary explicit necessary
inequality; this is a quantitative spectral exclusion statement. -/
theorem universalFredholm_zero_quantitative_constraint
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z = 0) :
    1 ≤ (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
  have hb := universalFredholm_spectral_origin_norm_le T z
  simpa only [hz, zero_sub, norm_neg, norm_one] using hb

/-- A quantitatively small trace-norm perturbation cannot create a
zero of the genuine universal Fredholm determinant at a fixed
complex parameter where the original determinant is separated from 0. -/
theorem universalFredholm_nonzero_of_traceNorm_perturbation
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hsmall :
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) <
        ‖fredholmDet T z‖) :
    fredholmDet (T + R) z ≠ 0 := by
  intro hz
  have hb := fredholmDet_add_traceNorm_bound T R z
  simp only [hz, zero_sub, norm_neg] at hb
  exact (not_lt_of_ge hb) hsmall

/-- Conversely, a trace-class perturbation producing a zero must
have at least the determinant separation prescribed by the true
global operator-perturbation bound. -/
theorem universalFredholm_new_zero_requires_large_perturbation
    (T R : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet (T + R) z = 0) :
    ‖fredholmDet T z‖ ≤
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) := by
  have hb := fredholmDet_add_traceNorm_bound T R z
  simpa only [hz, zero_sub, norm_neg] using hb

#print axioms Manuscript14Priority3.QuantitativeFredholmNonvanishing.universalFredholm_nonzero_of_quantitative_bound
#print axioms Manuscript14Priority3.QuantitativeFredholmNonvanishing.universalFredholm_zero_quantitative_constraint
#print axioms Manuscript14Priority3.QuantitativeFredholmNonvanishing.universalFredholm_nonzero_of_traceNorm_perturbation
#print axioms Manuscript14Priority3.QuantitativeFredholmNonvanishing.universalFredholm_new_zero_requires_large_perturbation

end Manuscript14Priority3.QuantitativeFredholmNonvanishing
