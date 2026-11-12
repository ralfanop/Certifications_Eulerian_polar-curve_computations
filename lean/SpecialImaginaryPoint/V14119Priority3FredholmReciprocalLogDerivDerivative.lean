import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLogDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Priority 3 — exact derivatives of the true universal Fredholm reciprocal and logarithmic derivative

For every complex CFC Schatten-S₁ trace-class Hilbert operator T,
the genuine universal Hilbert-compression-limit Fredholm determinant
f_T(z) = det_F(I+zT) is entire. The scalar reciprocal and its
logarithmic derivative are holomorphic wherever f_T(z) is nonzero.

We now certify exact pointwise FIRST DERIVATIVE formulas:
  (1/f_T)'(z) = -f_T'(z)/f_T(z)^2,
  (f_T'/f_T)'(z) = (f_T''(z)f_T(z) - f_T'(z)^2)/f_T(z)^2.
They apply without a normality, selfadjointness, positivity or
eigenvalue-enumeration assumption on T.

These are classical complex differentiation rules applied to the
independently certified actual infinite-dimensional determinant,
not a claim of novel calculus identities or a trace-resolvent theorem.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmReciprocalLogDerivDerivative

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.UniversalFredholmLogDerivative

/-- Exact analytic first derivative of the genuine Fredholm SCALAR
reciprocal on its nonvanishing complex spectral parameter domain. -/
theorem universalFredholm_reciprocal_deriv
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z ≠ 0) :
    deriv (fun w : ℂ => (fredholmDet T w)⁻¹) z =
      -(deriv (fredholmDet T) z) / (fredholmDet T z)^2 := by
  exact deriv_fun_inv'' ((universal_fredholmDet_entire T) z) hz

/-- Exact spectral derivative of the genuine universal Fredholm
logarithmic derivative away from the true determinant zeros.
The second derivative of f_T exists globally by its entire holomorphy. -/
theorem universalFredholm_logDeriv_deriv
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z ≠ 0) :
    deriv (logDeriv (fredholmDet T)) z =
      (deriv (deriv (fredholmDet T)) z * fredholmDet T z -
        deriv (fredholmDet T) z * deriv (fredholmDet T) z) /
          (fredholmDet T z)^2 := by
  change deriv (fun w : ℂ =>
    deriv (fredholmDet T) w / fredholmDet T w) z = _
  exact deriv_fun_div
    ((universalFredholmDet_deriv_entire T) z)
    ((universal_fredholmDet_entire T) z) hz

#print axioms Manuscript14Priority3.FredholmReciprocalLogDerivDerivative.universalFredholm_reciprocal_deriv
#print axioms Manuscript14Priority3.FredholmReciprocalLogDerivDerivative.universalFredholm_logDeriv_deriv

end Manuscript14Priority3.FredholmReciprocalLogDerivDerivative
