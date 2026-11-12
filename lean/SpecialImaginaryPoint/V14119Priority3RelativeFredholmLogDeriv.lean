import SpecialImaginaryPoint.V14119Priority3RelativeFredholmCocycle
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Priority 3 — exact logarithmic derivative identity for the true relative Fredholm determinant

For arbitrary complex CFC Schatten-S₁ Hilbert trace-class operators
T,S,U, define the GENUINE infinite-dimensional Hilbert-compression
Fredholm ratio R_(T,S)(z) = det_F(I+zT)/det_F(I+zS).

At every complex spectral parameter where the actual determinants
of T and S are nonzero, the logarithmic derivative is exactly the
DIFFERENCE of the two genuine Fredholm logarithmic derivatives.

Consequently, the relative logarithmic derivatives satisfy an
exact ADDITIVE COCYCLE for three arbitrary operators wherever
the three actual determinants do not vanish.

These are the precise complex analytic scalar identities underlying
a possible later relative trace-resolvent theorem. No operator
resolvent trace identity or zeta-relative determinant claim is made.
-/

noncomputable section

namespace Manuscript14Priority3.RelativeFredholmLogDeriv

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.RelativeUniversalFredholmScalar

/-- The logarithmic derivative of the TRUE relative scalar Fredholm
ratio equals exactly the difference of the genuine Fredholm
logarithmic derivatives, on the common nonzero spectral domain. -/
theorem universalFredholmRelativeScalar_logDeriv_eq_sub
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hT : fredholmDet T z ≠ 0) (hS : fredholmDet S z ≠ 0) :
    logDeriv (universalFredholmRelativeScalar T S) z =
      logDeriv (fredholmDet T) z - logDeriv (fredholmDet S) z := by
  change logDeriv (fun w : ℂ =>
    fredholmDet T w / fredholmDet S w) z = _
  exact logDeriv_fun_div z hT hS
    ((universal_fredholmDet_entire T) z)
    ((universal_fredholmDet_entire S) z)

/-- The relative logarithmic derivatives satisfy exact additive
cocycle composition, valid for ANY three trace-class Hilbert operators
on their common nonvanishing complex spectral parameter domain. -/
theorem universalFredholmRelativeScalar_logDeriv_cocycle
    (T S U : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hT : fredholmDet T z ≠ 0) (hS : fredholmDet S z ≠ 0)
    (hU : fredholmDet U z ≠ 0) :
    logDeriv (universalFredholmRelativeScalar T S) z +
      logDeriv (universalFredholmRelativeScalar S U) z =
        logDeriv (universalFredholmRelativeScalar T U) z := by
  rw [universalFredholmRelativeScalar_logDeriv_eq_sub T S z hT hS,
    universalFredholmRelativeScalar_logDeriv_eq_sub S U z hS hU,
    universalFredholmRelativeScalar_logDeriv_eq_sub T U z hT hU]
  ring

#print axioms Manuscript14Priority3.RelativeFredholmLogDeriv.universalFredholmRelativeScalar_logDeriv_eq_sub
#print axioms Manuscript14Priority3.RelativeFredholmLogDeriv.universalFredholmRelativeScalar_logDeriv_cocycle

end Manuscript14Priority3.RelativeFredholmLogDeriv
