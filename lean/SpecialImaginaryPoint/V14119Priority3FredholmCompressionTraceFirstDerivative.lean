import SpecialImaginaryPoint.V14119Priority3FredholmCompressionDerivativesConverge
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Priority 3 — finite compression determinant derivative equals finite matrix trace

For every complex square matrix M, without normality, positivity,
selfadjointness or invertibility, the ACTUAL determinant pencil
  D_M(z) = det(I + zM)
has the exact first-order derivative
  D'_M(0) = tr(M).

The proof is algebraically grounded in Mathlib's identity
  Matrix.derivative_det_one_add_X_smul,
together with the exact polynomial representation of det(I+zM).

Applying this to the TRUE finite CFC-S₁ Hilbert compression matrices
M_N(T) gives an exact finite trace identity and, using the newly
certified complex-analytic local-uniform derivative limit, proves
  lim_N tr(M_N(T)) = (d/dz)det_F(I+zT)|_(z=0).

THIS IS NOT YET a proof that the limit equals an independently
defined CFC trace of an arbitrary trace-class T. Such an
identification is a separate operatorial obligation.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmCompressionTraceFirstDerivative

open Filter Topology Set Matrix Polynomial
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteShiftEntirePolynomial
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.FredholmCompressionDerivativesConverge

/-- Exact first derivative at zero of the finite complex
determinant pencil, for EVERY matrix including arbitrary
nonnormal or singular matrices. -/
theorem finite_matrix_det_shift_deriv_zero
    (N : ℕ) (M : Matrix (Fin N) (Fin N) ℂ) :
    deriv (fun z : ℂ => (1 + z • M).det) 0 = M.trace := by
  have hpoly :
      (fun z : ℂ => (1 + z • M).det) =
        (fun z : ℂ => (determinantPolynomial N M).eval z) := by
    funext z
    exact (determinantPolynomial_eval N M z).symm
  rw [hpoly, (determinantPolynomial N M).deriv]
  exact Matrix.derivative_det_one_add_X_smul M

/-- Exact matrix trace identity for the ACTUAL N-dimensional CFC-S₁
Hilbert-compression Fredholm determinant polynomial. -/
theorem finiteFredholm_compression_deriv_zero_eq_trace
    (N : ℕ) (T : ProbabilisticTheory.TraceClass H) :
    deriv (finiteDeterminant N T) 0 = (compressedCFC N T).trace := by
  change deriv (fun z : ℂ => (1 + z • compressedCFC N T).det) 0 = _
  exact finite_matrix_det_shift_deriv_zero N (compressedCFC N T)

/-- The complex matrix traces of the ACTUAL finite Hilbert
compressions converge to the spectral derivative at zero
of the genuine universal CFC-S₁ Fredholm determinant. -/
theorem finiteFredholm_compression_trace_tendsto_universal_deriv_zero
    (T : ProbabilisticTheory.TraceClass H) :
    Tendsto (fun N : ℕ => (compressedCFC N T).trace) atTop
      (𝓝 (deriv (fredholmDet T) 0)) := by
  have h := finiteFredholm_derivatives_pointwise_tendsto T 0
  simpa only [finiteFredholm_compression_deriv_zero_eq_trace] using h

#print axioms Manuscript14Priority3.FredholmCompressionTraceFirstDerivative.finite_matrix_det_shift_deriv_zero
#print axioms Manuscript14Priority3.FredholmCompressionTraceFirstDerivative.finiteFredholm_compression_deriv_zero_eq_trace
#print axioms Manuscript14Priority3.FredholmCompressionTraceFirstDerivative.finiteFredholm_compression_trace_tendsto_universal_deriv_zero

end Manuscript14Priority3.FredholmCompressionTraceFirstDerivative
