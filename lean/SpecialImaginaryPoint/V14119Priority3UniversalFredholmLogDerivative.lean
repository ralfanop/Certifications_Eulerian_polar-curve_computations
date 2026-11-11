import SpecialImaginaryPoint.V14119Priority3MeromorphicFredholmReciprocal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Priority 3 — true universal Fredholm logarithmic derivative

For any complex CFC Schatten-S₁ Hilbert operator T, the genuine
Hilbert-compression-limit Fredholm determinant f_T(z) = det_F(I+zT)
is entire. Its complex derivative f_T' is also entire, and its
logarithmic derivative f_T'/f_T is globally MEROMORPHIC.

The logarithmic derivative is holomorphic on the open dense
set of nonzero Fredholm spectral parameters. This applies without
normality, selfadjointness, positivity or compact diagonalization
assumptions. There is no claim of a trace-resolvent identity here.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmLogDerivative

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.GenericFredholmSpectralParameters
open Manuscript14Priority3.MeromorphicFredholmReciprocal

/-- The derivative in z of the genuine universal Fredholm
determinant is entire for arbitrary trace-class Hilbert T. -/
theorem universalFredholmDet_deriv_entire
    (T : ProbabilisticTheory.TraceClass H) :
    Differentiable ℂ (deriv (fredholmDet T)) := by
  exact (universal_fredholmDet_entire T).deriv

/-- The genuine spectral Fredholm logarithmic derivative is
globally meromorphic on the whole complex plane. -/
theorem universalFredholm_logDeriv_meromorphicOn
    (T : ProbabilisticTheory.TraceClass H) :
    MeromorphicOn (logDeriv (fredholmDet T))
      (Set.univ : Set ℂ) := by
  exact ((universalFredholmDet_analyticOnNhd T).meromorphicOn).logDeriv

/-- Where the genuine Fredholm determinant is nonzero, its
logarithmic derivative is complex differentiable. -/
theorem universalFredholm_logDeriv_differentiableAt
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z ≠ 0) :
    DifferentiableAt ℂ (logDeriv (fredholmDet T)) z := by
  change DifferentiableAt ℂ
    (fun w : ℂ => deriv (fredholmDet T) w / fredholmDet T w) z
  exact ((universalFredholmDet_deriv_entire T) z).div
    ((universal_fredholmDet_entire T) z) hz

/-- The logarithmic derivative of the true universal Fredholm
determinant is holomorphic throughout the open dense nonzero set. -/
theorem universalFredholm_logDeriv_differentiableOn
    (T : ProbabilisticTheory.TraceClass H) :
    DifferentiableOn ℂ (logDeriv (fredholmDet T))
      (universalFredholmNonzeroSet T) := by
  intro z hz
  exact (universalFredholm_logDeriv_differentiableAt T z
    ((mem_universalFredholmNonzeroSet_iff T z).mp hz)).differentiableWithinAt

#print axioms Manuscript14Priority3.UniversalFredholmLogDerivative.universalFredholmDet_deriv_entire
#print axioms Manuscript14Priority3.UniversalFredholmLogDerivative.universalFredholm_logDeriv_meromorphicOn
#print axioms Manuscript14Priority3.UniversalFredholmLogDerivative.universalFredholm_logDeriv_differentiableAt
#print axioms Manuscript14Priority3.UniversalFredholmLogDerivative.universalFredholm_logDeriv_differentiableOn

end Manuscript14Priority3.UniversalFredholmLogDerivative
