import SpecialImaginaryPoint.V14119Priority3RelativeUniversalFredholmScalar
import Mathlib.Analysis.Meromorphic.Order

/-!
# Priority 3 — exact meromorphic order of genuine relative Fredholm determinants

For any arbitrary complex CFC Schatten-S₁ Hilbert trace-class operators
T and S, including nonnormal and nonselfadjoint operators, the actual
infinite-dimensional Hilbert-compression-limit Fredholm functions
f_T(z), f_S(z) are entire and not identically zero (normalized to 1
at z=0).

Their genuine relative scalar determinant ratio R_(T,S)=f_T/f_S
is globally meromorphic. At EVERY complex shift z, including spectral
zeros and poles, its meromorphic order is the difference of those of
the two actual operatorial Fredholm determinants:
  ord_z R_(T,S) = ord_z f_T - ord_z f_S.

No equality with any relative zeta-regularized determinant is asserted.
-/

noncomputable section

namespace Manuscript14Priority3.RelativeFredholmMeromorphicOrder

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.MeromorphicFredholmReciprocal
open Manuscript14Priority3.RelativeUniversalFredholmScalar

/-- The EXACT local meromorphic order of the true universal relative
Fredholm scalar determinant is the difference of two individually
true infinite-dimensional Fredholm meromorphic orders. -/
theorem universalFredholmRelativeScalar_meromorphicOrderAt
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    meromorphicOrderAt (universalFredholmRelativeScalar T S) z =
      meromorphicOrderAt (fredholmDet T) z -
        meromorphicOrderAt (fredholmDet S) z := by
  change meromorphicOrderAt ((fredholmDet T) / (fredholmDet S)) z = _
  exact meromorphicOrderAt_div
    ((universalFredholmDet_analyticOnNhd T).meromorphicOn z (Set.mem_univ z))
    ((universalFredholmDet_analyticOnNhd S).meromorphicOn z (Set.mem_univ z))

#print axioms Manuscript14Priority3.RelativeFredholmMeromorphicOrder.universalFredholmRelativeScalar_meromorphicOrderAt

end Manuscript14Priority3.RelativeFredholmMeromorphicOrder
