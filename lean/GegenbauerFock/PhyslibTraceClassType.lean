import GegenbauerFock.PhyslibHilbertSchmidtCompat

/-!
# V007: typed infinite-dimensional Physlib-compatible trace-class operators

This is a staged, kernel-checkable port of the **carrier** of the
PhyslibAlpha Banach trace class:
Tom Ole Diem, PhyslibAlpha/ProbabilisticTheory/HilbertSpace/
TraceClass/Banach.lean (Apache-2.0).

The mathematical `IsTraceClass` and `traceNorm` predicates were
already ported and certified in PhyslibTraceClassCompat.lean.

This module establishes the separate concrete trace-class type,
coercion, constructor, and the exact norm formula for the actual
ultraspherical Gram. It deliberately does NOT assert a normed
additive group, a Banach instance, or the two-sided ideal laws
before porting their requisite nontrivial general proofs.
The original project toolchain and Mathlib SHA stay pinned.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The carrier of Physlib's trace-class operator type, consisting of
all bounded Hilbert-space endomorphisms with summable CFC absolute
value diagonals. -/
def TraceClass (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] : Type _ :=
  {T : H →L[ℂ] H // IsTraceClass T}

namespace TraceClass

/-- A trace-class operator carries the necessary convergence proof. -/
theorem isTraceClass_coe (T : TraceClass H) :
    IsTraceClass T.1 := T.2

/-- Construct the typed trace-class operator from a proved predicate. -/
def ofOperator (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    TraceClass H := ⟨T, hT⟩

@[simp] theorem ofOperator_coe (T : H →L[ℂ] H)
    (hT : IsTraceClass T) :
    (ofOperator T hT).1 = T := rfl

/-- Trace norm of the typed operator using Physlib-compatible CFC
absolute value; no normed-group instance is silently assumed. -/
noncomputable def traceNormValue (T : TraceClass H) : ℝ :=
  ProbabilisticTheory.traceNorm T.1 T.2

@[simp] theorem traceNormValue_ofOperator (T : H →L[ℂ] H)
    (hT : IsTraceClass T) :
    traceNormValue (ofOperator T hT) =
      ProbabilisticTheory.traceNorm T hT := rfl

end TraceClass

#print axioms ProbabilisticTheory.TraceClass.isTraceClass_coe
#print axioms ProbabilisticTheory.TraceClass.traceNormValue_ofOperator

end ProbabilisticTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The genuine nontruncated positive Gram C†C, as an actual
member of the infinite-dimensional trace-class carrier. -/
noncomputable def gramTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.TraceClass
      (Lp ℂ 2 (Ultraspherical.measure lam)) :=
  ProbabilisticTheory.TraceClass.ofOperator
    (gram lam alpha hlam ha)
    (gram_isTraceClass lam alpha hlam ha)

@[simp] theorem gramTraceClass_coe
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (gramTraceClass lam alpha hlam ha).1 =
      gram lam alpha hlam ha := rfl

/-- The true trace-norm value of the typed Gram is Kummer's series. -/
theorem gramTraceClass_traceNormValue_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.TraceClass.traceNormValue
        (gramTraceClass lam alpha hlam ha) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
  gram_traceNorm_eq_kummer lam alpha hlam ha

/-- The typed Gram trace-norm value agrees with the norm-summable
positive rank-one operator mass. -/
theorem gramTraceClass_traceNormValue_eq_nuclearMass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.TraceClass.traceNormValue
        (gramTraceClass lam alpha hlam ha) =
      ∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖ :=
  gram_traceNorm_eq_positiveNuclearMass lam alpha hlam ha

/-- Gamma-normalized Mathlib's genuine regularized complex HG function
is the exact trace-norm value of the typed Gram. -/
theorem gramTraceClass_traceNormValue_eq_regularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((ProbabilisticTheory.TraceClass.traceNormValue
        (gramTraceClass lam alpha hlam ha)) : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) :=
  gram_traceNorm_eq_mathlibRegularizedKummer lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_coe
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_traceNormValue_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_traceNormValue_eq_nuclearMass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramTraceClass_traceNormValue_eq_regularizedKummer

end GegenbauerFock.GeneralUltrasphericalFock
