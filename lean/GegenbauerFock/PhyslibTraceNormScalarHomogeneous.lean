import GegenbauerFock.PhyslibTraceNormHomogeneity
import GegenbauerFock.PhyslibTraceClassPointed

/-!
# V007 — exact trace-norm homogeneity on the proof-carrying S1 type

The non-selfadjoint scalar trace-norm theorem has already been
developed in PhyslibTraceNormHomogeneity, which uses the genuine
basis-independent CFC absolute-value trace.  This module does NOT
duplicate that proof: it transports the results to the actual
`ProbabilisticTheory.TraceClass H` operator subtype and its real
trace norm, using its existing scalar and negation actions.

The full additive closure, triangle inequality, and S1 Banach
completeness remain separate obligations.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact absolute homogeneity of the genuine trace norm of any
proof-carrying, possibly non-selfadjoint trace-class operator. -/
theorem traceNorm_smul_general (c : ℂ) (T : TraceClass H) :
    traceNorm H (c • T) = ‖c‖ * traceNorm H T :=
  ProbabilisticTheory.traceNorm_smul c T.2

/-- The genuine trace norm of a proof-carrying S1 operator
is unchanged under additive negation. -/
theorem traceNorm_neg_general (T : TraceClass H) :
    traceNorm H (-T) = traceNorm H T :=
  ProbabilisticTheory.traceNorm_neg_of_isTraceClass T.2

#print axioms ProbabilisticTheory.TraceClass.traceNorm_smul_general
#print axioms ProbabilisticTheory.TraceClass.traceNorm_neg_general

end ProbabilisticTheory.TraceClass
