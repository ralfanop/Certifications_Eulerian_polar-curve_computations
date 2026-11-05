import GegenbauerFock.PhyslibHilbertSchmidtCompat

/-!
# V007 — source-compatible trace-class operator subtype (incremental port)

This file packages the kernel-checked Physlib-compatible S₁ membership
predicate `ProbabilisticTheory.IsTraceClass` as a reusable
operator-with-proof type, and constructs the actual ultraspherical Gram
as an element of that type.

This is an *operator subtype*, not yet Physlib's full trace-normed Banach
space. The general additive closure, triangle inequality, and
completeness needed for the genuine normed-space structure are distinct
proof obligations. No Mathlib/Lean version changes or hidden axioms.
-/

noncomputable section

namespace ProbabilisticTheory

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact underlying set of the (not-yet-normed) Physlib-compatible
trace-class operators, with a proof of genuine CFC-absolute diagonal
summability. -/
def TraceClass (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Type _ :=
  { T : H →L[ℂ] H // IsTraceClass T }

namespace TraceClass

/-- Construct a trace-class element from any bounded operator carrying
its trace-class certification. -/
def ofOperator (T : H →L[ℂ] H) (h : IsTraceClass T) :
    TraceClass H := ⟨T, h⟩

/-- The underlying continuous operator of a trace-class element. -/
def operator (T : TraceClass H) : H →L[ℂ] H := T.1

/-- Certified class-trace norm, using precisely Physlib's CFC absolute
value and Hilbert-basis diagonal summation. -/
noncomputable def traceNorm (T : TraceClass H) : ℝ :=
  ProbabilisticTheory.traceNorm T.1 T.2

@[simp]
theorem ofOperator_operator
    (T : H →L[ℂ] H) (h : IsTraceClass T) :
    operator H (ofOperator H T h) = T := rfl

@[simp]
theorem traceNorm_ofOperator
    (T : H →L[ℂ] H) (h : IsTraceClass T) :
    traceNorm H (ofOperator H T h) =
      ProbabilisticTheory.traceNorm T h := rfl

#print axioms ProbabilisticTheory.TraceClass.traceNorm_ofOperator

end TraceClass
end ProbabilisticTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The true nontruncated ultraspherical Gram, as an element of the
Physlib-compatible trace-class type, not merely a Prop. -/
noncomputable def gramTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.TraceClass
      (Lp ℂ 2 (Ultraspherical.measure lam)) :=
  ProbabilisticTheory.TraceClass.ofOperator
    _ (gram lam alpha hlam ha)
      (gram_isTraceClass lam alpha hlam ha)

@[simp]
theorem gramTraceClass_operator
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.TraceClass.operator _
      (gramTraceClass lam alpha hlam ha) =
      gram lam alpha hlam ha := rfl

/-- The real, witness-carrying trace-class element has exactly the
Kummer trace norm, with no extra hypothesis or formal placeholder. -/
theorem gramTraceClass_traceNorm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.TraceClass.traceNorm _
      (gramTraceClass lam alpha hlam ha) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
  gram_traceNorm_eq_kummer lam alpha hlam ha

/-- The trace-class package also retains the fully certified
Gamma-corrected Mathlib regularized confluent hypergeometric value. -/
theorem gramTraceClass_traceNorm_eq_mathlibRegularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((ProbabilisticTheory.TraceClass.traceNorm _
      (gramTraceClass lam alpha hlam ha)) : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) :=
  gram_traceNorm_eq_mathlibRegularizedKummer lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_operator
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_traceNorm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_traceNorm_eq_mathlibRegularizedKummer

end GegenbauerFock.GeneralUltrasphericalFock
