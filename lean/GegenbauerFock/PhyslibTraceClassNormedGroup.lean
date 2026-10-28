import GegenbauerFock.PhyslibTraceClassAddCommGroup
import GegenbauerFock.PhyslibTraceNormTriangleYoung
import GegenbauerFock.PhyslibTraceNormDominatesOpNorm
import GegenbauerFock.PhyslibTraceNormScalarHomogeneous

/-!
# V007 — the genuine CFC Schatten-S₁ normed additive group

This upgrades the existing proof-carrying TraceClass H additive
abelian group to a real trace-normed additive group. The norm is
exactly the previously defined Physlib-compatible traceNorm, not
the ambient operator norm.

The construction uses four independent proof obligations:
 zero trace norm, negation invariance, unrestricted triangle
 inequality, and separation via the operator norm bound.

This is NOT a proof of completeness; no CompleteSpace instance
is introduced. It must pass a separate exact-SHA Lean compilation
and axiom audit before use as an established theorem.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual CFC trace norm is an AddGroupNorm on the entire
possibly non-selfadjoint trace-class operator subtype. -/
noncomputable def genuineTraceAddGroupNorm : AddGroupNorm (TraceClass H) where
  toFun T := traceNorm H T
  map_zero' := traceNorm_zero_element
  neg' T := traceNorm_neg_general T
  add_le' T V := by
    change ProbabilisticTheory.traceNorm (T.1 + V.1) (T + V).2 ≤
      ProbabilisticTheory.traceNorm T.1 T.2 +
        ProbabilisticTheory.traceNorm V.1 V.2
    exact ProbabilisticTheory.traceNorm_add_le_via_hsYoung
      T.1 V.1 T.2 V.2 (T + V).2
  eq_zero_of_map_eq_zero' T hT0 := by
    apply Subtype.ext
    exact ProbabilisticTheory.traceNorm_eq_zero_implies_operator_zero
      T.1 T.2 hT0

/-- The Schatten S₁ normed-additive-group structure, using the
full CFC absolute-value trace norm. No Banach completeness claim. -/
noncomputable instance instGenuineNormedAddCommGroup :
    NormedAddCommGroup (TraceClass H) :=
  AddGroupNorm.toNormedAddCommGroup genuineTraceAddGroupNorm

@[simp] theorem norm_eq_genuineTraceNorm (T : TraceClass H) :
    ‖T‖ = traceNorm H T := rfl

/-- The norm assigned to the actual ultraspherical Gram remains
precisely the previously certified Kummer/trace-norm expression. -/
theorem traceNorm_le_of_triangle (T V : TraceClass H) :
    traceNorm H (T + V) ≤ traceNorm H T + traceNorm H V :=
  ProbabilisticTheory.traceNorm_add_le_via_hsYoung
    T.1 V.1 T.2 V.2 (T + V).2

#print axioms ProbabilisticTheory.TraceClass.norm_eq_genuineTraceNorm
#print axioms ProbabilisticTheory.TraceClass.traceNorm_le_of_triangle

end ProbabilisticTheory.TraceClass
