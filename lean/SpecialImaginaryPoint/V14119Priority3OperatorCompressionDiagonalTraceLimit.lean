import SpecialImaginaryPoint.V14119Priority3FredholmCompressionTraceFirstDerivative

/-!
# Priority 3 — finite diagonal trace of the genuine Hilbert compression

For arbitrary complex CFC Schatten-S₁ trace-class operators T, not
assumed normal or selfadjoint, the actual N-dimensional Hilbert
compression M_N(T) has its finite matrix trace equal to the
unmodified finite Hilbert basis diagonal sum

 tr(M_N(T)) = ∑ i : Fin N, ⟪b_i,T b_i⟫_ℂ.

Together with the certified convergence of finite compression traces
to the derivative of the genuine universal Fredholm determinant,
this proves the finite diagonal basis sums converge as N→∞ to
(d/dz) det_F(I+zT) at z=0.

No unconditional equality to an independently defined abstract
trace-class trace is asserted: that remains a separate obligation.
-/

noncomputable section

namespace Manuscript14Priority3.OperatorCompressionDiagonalTraceLimit

open Filter Topology Set InnerProductSpace Matrix
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.FredholmCompressionTraceFirstDerivative
open Manuscript14Priority3.UniversalFredholmExistence

/-- The exact basis-diagonal expansion of the finite matrix trace
of an arbitrary genuine CFC-S₁ Hilbert compression. -/
theorem compression_trace_eq_finite_basis_diagonal_sum
    (N : ℕ) (T : ProbabilisticTheory.TraceClass H) :
    (compressedCFC N T).trace =
      ∑ i : Fin N, inner ℂ (b i.val) (T.1 (b i.val)) := by
  simp [Matrix.trace, Matrix.diag, compressedCFC]

/-- The finite actual complex Hilbert-basis diagonal sums converge
to the derivative at zero of the universal CFC-S₁ Fredholm determinant. -/
theorem finite_basis_diagonal_sum_tendsto_fredholm_deriv_zero
    (T : ProbabilisticTheory.TraceClass H) :
    Tendsto
      (fun N : ℕ => ∑ i : Fin N, inner ℂ (b i.val) (T.1 (b i.val)))
      atTop (𝓝 (deriv (fredholmDet T) 0)) := by
  simpa only [compression_trace_eq_finite_basis_diagonal_sum] using
    finiteFredholm_compression_trace_tendsto_universal_deriv_zero T

#print axioms Manuscript14Priority3.OperatorCompressionDiagonalTraceLimit.compression_trace_eq_finite_basis_diagonal_sum
#print axioms Manuscript14Priority3.OperatorCompressionDiagonalTraceLimit.finite_basis_diagonal_sum_tendsto_fredholm_deriv_zero

end Manuscript14Priority3.OperatorCompressionDiagonalTraceLimit
