import SpecialImaginaryPoint.V14119Priority3RelativeFredholmLogDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Priority 3 — exact derivative at zero of genuine relative scalar Fredholm determinants

For arbitrary complex CFC Schatten-S₁ trace-class Hilbert operators T and S,
let the ACTUAL infinite-dimensional Hilbert-compression-limit Fredholm
ratio be R_(T,S)(z) = det_F(I+zT)/det_F(I+zS).

The independently certified true normalization f_T(0)=f_S(0)=1
and entire spectral holomorphy imply the exact relative first-derivative
and logarithmic-derivative identities at the origin:
 R'_(T,S)(0) = f'_T(0)-f'_S(0)
 and (R'_(T,S)/R_(T,S))(0) = f'_T(0)-f'_S(0).

This is an identity of SCALAR determinant derivatives, not an assertion
that either derivative is an independently defined trace on all S₁,
nor an equivalence with a relative zeta-regularized determinant.
-/

noncomputable section

namespace Manuscript14Priority3.RelativeFredholmDerivZero

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.RelativeUniversalFredholmScalar

/-- Exact first spectral derivative at zero of the actual relative
universal trace-class Hilbert Fredholm determinant ratio. -/
theorem universalFredholmRelativeScalar_deriv_zero
    (T S : ProbabilisticTheory.TraceClass H) :
    deriv (universalFredholmRelativeScalar T S) 0 =
      deriv (fredholmDet T) 0 - deriv (fredholmDet S) 0 := by
  change deriv (fun w : ℂ => fredholmDet T w / fredholmDet S w) 0 = _
  rw [deriv_fun_div ((universal_fredholmDet_entire T) 0)
    ((universal_fredholmDet_entire S) 0)
    (by rw [fredholmDet_zero]; exact one_ne_zero)]
  simp only [fredholmDet_zero, mul_one, one_mul, one_pow, div_one]

/-- The genuine relative scalar Fredholm logarithmic derivative
at z=0 is exactly the difference of the two determinant derivatives. -/
theorem universalFredholmRelativeScalar_logDeriv_zero
    (T S : ProbabilisticTheory.TraceClass H) :
    logDeriv (universalFredholmRelativeScalar T S) 0 =
      deriv (fredholmDet T) 0 - deriv (fredholmDet S) 0 := by
  rw [logDeriv_apply, universalFredholmRelativeScalar_zero, div_one]
  exact universalFredholmRelativeScalar_deriv_zero T S

#print axioms Manuscript14Priority3.RelativeFredholmDerivZero.universalFredholmRelativeScalar_deriv_zero
#print axioms Manuscript14Priority3.RelativeFredholmDerivZero.universalFredholmRelativeScalar_logDeriv_zero

end Manuscript14Priority3.RelativeFredholmDerivZero
