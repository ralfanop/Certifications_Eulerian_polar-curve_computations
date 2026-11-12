import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLogDerivative
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Priority 3 — a genuine relative scalar Fredholm determinant for trace-class pairs

For ANY complex CFC Schatten-S₁ trace-class Hilbert operators T and S
(including nonnormal and nonselfadjoint operators), the *actual*
infinite-dimensional Hilbert-compression-limit Fredholm determinants
f_T(z)=det_F(I+zT) and f_S(z)=det_F(I+zS) are entire and satisfy
f_T(0)=f_S(0)=1.

The genuine RELATIVE SCALAR Fredholm determinant ratio
R_(T,S)(z) := f_T(z)/f_S(z) is therefore meromorphic globally,
holomorphic at every complex parameter where f_S does not vanish,
and exactly normalized by R_(T,S)(0)=1.

This is a ratio of already constructed genuine Fredholm determinants.
It does NOT assert any equality with a relative zeta-regularized
determinant nor an operator resolvent trace formula.
-/

noncomputable section

namespace Manuscript14Priority3.RelativeUniversalFredholmScalar

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.MeromorphicFredholmReciprocal
open Manuscript14Priority3.GenericFredholmSpectralParameters

/-- The relative SCALAR determinant of two genuine universal CFC-S₁
Fredholm operators, never a finite auxiliary polynomial product. -/
def universalFredholmRelativeScalar
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ) : ℂ :=
  fredholmDet T z / fredholmDet S z

/-- The genuine relative scalar Fredholm determinant is exactly
normalized at the origin for every pair of trace-class operators. -/
theorem universalFredholmRelativeScalar_zero
    (T S : ProbabilisticTheory.TraceClass H) :
    universalFredholmRelativeScalar T S 0 = 1 := by
  simp only [universalFredholmRelativeScalar, fredholmDet_zero, div_self (one_ne_zero : (1 : ℂ) ≠ 0)]

/-- Any ratio of the actual universal Fredholm determinants of
two arbitrary trace-class operators is globally meromorphic. -/
theorem universalFredholmRelativeScalar_meromorphicOn
    (T S : ProbabilisticTheory.TraceClass H) :
    MeromorphicOn (universalFredholmRelativeScalar T S)
      (Set.univ : Set ℂ) := by
  change MeromorphicOn ((fredholmDet T) / (fredholmDet S)) (Set.univ : Set ℂ)
  exact ((universalFredholmDet_analyticOnNhd T).meromorphicOn).div
    ((universalFredholmDet_analyticOnNhd S).meromorphicOn)

/-- The true relative scalar Fredholm determinant is holomorphic
at every spectral shift where its denominator determinant is nonzero. -/
theorem universalFredholmRelativeScalar_differentiableAt
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet S z ≠ 0) :
    DifferentiableAt ℂ (universalFredholmRelativeScalar T S) z := by
  change DifferentiableAt ℂ (fun w : ℂ => fredholmDet T w / fredholmDet S w) z
  exact ((universal_fredholmDet_entire T) z).div
    ((universal_fredholmDet_entire S) z) hz

/-- The relative genuine Fredholm determinant is holomorphic on
the entire open dense complex nonzero domain of its denominator. -/
theorem universalFredholmRelativeScalar_differentiableOn
    (T S : ProbabilisticTheory.TraceClass H) :
    DifferentiableOn ℂ (universalFredholmRelativeScalar T S)
      (universalFredholmNonzeroSet S) := by
  intro z hz
  exact (universalFredholmRelativeScalar_differentiableAt T S z
    ((mem_universalFredholmNonzeroSet_iff S z).mp hz)).differentiableWithinAt

#print axioms Manuscript14Priority3.RelativeUniversalFredholmScalar.universalFredholmRelativeScalar_zero
#print axioms Manuscript14Priority3.RelativeUniversalFredholmScalar.universalFredholmRelativeScalar_meromorphicOn
#print axioms Manuscript14Priority3.RelativeUniversalFredholmScalar.universalFredholmRelativeScalar_differentiableAt
#print axioms Manuscript14Priority3.RelativeUniversalFredholmScalar.universalFredholmRelativeScalar_differentiableOn

end Manuscript14Priority3.RelativeUniversalFredholmScalar
