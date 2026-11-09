import SpecialImaginaryPoint.V14119Priority3DirichletDiagonal
import GegenbauerFock.RealComplexPositiveSpectralAutomaticTraceClassBridge
import GegenbauerFock.PositiveTraceDiagonalSpectralBridge

/-!
# Priority 3 — genuine source-compatible CFC trace-class inverse model

Builds on the ACTUAL bounded positive Dirichlet spectral inverse operator
on complex l² from V14119Priority3DirichletDiagonal.

This proves its CFC-absolute trace class and trace norm; it does NOT
yet identify the operator with the differential Dirichlet problem on
L²(0,1), nor establish Fredholm/zeta determinant identities.
-/

noncomputable section

namespace Manuscript14Priority3.TraceClassModel
open Filter Topology InnerProductSpace
open scoped ComplexOrder

/-- The actual positive bounded operator is in the full CFC-absolute
(source-compatible Physlib) trace class, not merely a spectral sequence. -/
theorem inverse_isTraceClass :
    ProbabilisticTheory.IsTraceClass inverse := by
  have hs : Summable (fun n : ℕ =>
      (inner ℂ (b n) (inverse (b n))).re) :=
    σ_summable.congr (fun n => (inverse_diagonal n).symm)
  exact GegenbauerFock.Ultraspherical.complex_nonneg_isTraceClass_of_summable_natBasis_diagonal
      inverse inverse_nonneg b hs

/-- The genuine CFC trace norm equals the sum of positive Dirichlet
inverse eigenvalues, independently of the trace-class witness basis. -/
theorem inverse_traceNorm_eq :
    ProbabilisticTheory.traceNorm inverse inverse_isTraceClass =
      ∑' n : ℕ, σ n := by
  rw [GegenbauerFock.HilbertSchmidtBasis.positiveTrace_traceNorm_eq_diagonal_tsum
      inverse inverse_isTraceClass inverse_nonneg b]
  exact tsum_congr inverse_diagonal

#print axioms Manuscript14Priority3.TraceClassModel.σ_summable
#print axioms Manuscript14Priority3.TraceClassModel.term_summable
#print axioms Manuscript14Priority3.TraceClassModel.inverse_eigen
#print axioms Manuscript14Priority3.TraceClassModel.inverse_nonneg
#print axioms Manuscript14Priority3.TraceClassModel.inverse_diagonal
#print axioms Manuscript14Priority3.TraceClassModel.inverse_isTraceClass
#print axioms Manuscript14Priority3.TraceClassModel.inverse_traceNorm_eq

end Manuscript14Priority3.TraceClassModel
