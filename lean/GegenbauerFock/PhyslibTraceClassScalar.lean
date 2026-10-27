import GegenbauerFock.PhyslibTraceNormCore

/-!
# V007 — scalar-module closure of the source-compatible Physlib trace class

The source-compatible infinite-dimensional `IsTraceClass` predicate
has a genuine CFC absolute-value witness. These are direct adaptations
of the elementary algebraic closure results from Tom Ole Diem's
PhyslibAlpha TraceClass/Banach.lean (Apache-2.0), compiled against
V007's *unchanged* Lean v4.35.0-rc3 and pinned Mathlib.

The elementary zero and nonnegativity lemmas now come from the canonical
PhyslibTraceNormCore import, eliminating duplicate global declarations.
This is a strict incremental step toward, not a false assertion of,
the full additive normed Banach trace-class API: additive closure,
norm triangle inequality, and completeness remain separate.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Complex scalar multiplication preserves the full
infinite-dimensional CFC-absolute trace-class predicate. -/
theorem isTraceClass_smul (c : ℂ) {T : H →L[ℂ] H}
    (hT : IsTraceClass T) : IsTraceClass (c • T) := by
  obtain ⟨w, b, hb⟩ := hT
  refine ⟨w, b, ?_⟩
  have habs : CFC.abs (c • T) = ‖c‖ • CFC.abs T :=
    CFC.abs_smul c T
  have heq : ∀ i : w,
      (inner ℂ (b i) (CFC.abs (c • T) (b i))).re =
        ‖c‖ * (inner ℂ (b i) (CFC.abs T (b i))).re := by
    intro i
    rw [habs, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp [Complex.mul_re]
  simpa only [heq] using hb.mul_left ‖c‖

/-- The negative of any trace-class operator is trace class. -/
theorem isTraceClass_neg {T : H →L[ℂ] H}
    (hT : IsTraceClass T) : IsTraceClass (-T) := by
  have h := isTraceClass_smul (-1 : ℂ) hT
  rwa [neg_one_smul] at h

/-- The trace-norm witness proof is propositionally irrelevant; this
is the exact elementary lemma used by upstream Physlib Banach.lean. -/
theorem traceNorm_congr {T : H →L[ℂ] H}
    {h₁ h₂ : IsTraceClass T} :
    traceNorm T h₁ = traceNorm T h₂ := by
  have hh : h₁ = h₂ := Subsingleton.elim _ _
  rw [hh]

#print axioms ProbabilisticTheory.traceNorm_congr
#print axioms ProbabilisticTheory.traceNorm_nonneg

#print axioms ProbabilisticTheory.isTraceClass_zero
#print axioms ProbabilisticTheory.isTraceClass_smul
#print axioms ProbabilisticTheory.isTraceClass_neg

end ProbabilisticTheory

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Canonical scalar action on the real, proof-carrying source-compatible
trace-class subtype, provided by the now-proved scalar closure. -/
noncomputable instance : SMul ℂ (TraceClass H) where
  smul c T := ⟨c • T.1, ProbabilisticTheory.isTraceClass_smul c T.2⟩


/-- Negation of a genuinely CFC trace-class operator, with its S₁ witness. -/
noncomputable instance : Neg (TraceClass H) where
  neg T := ⟨-T.1, ProbabilisticTheory.isTraceClass_neg T.2⟩

@[simp] theorem neg_operator (T : TraceClass H) :
    ((-T : TraceClass H).1) = -T.1 := rfl

#print axioms ProbabilisticTheory.TraceClass.neg_operator

/-- Scalar multiplication of proof-carrying trace-class operators
agrees *definitionally* with scalar multiplication of bounded maps. -/
@[simp] theorem smul_operator (c : ℂ) (T : TraceClass H) :
    ((c • T : TraceClass H).1) = c • T.1 := rfl

/-- The actual Gram trace-class element remains in the subtype
after arbitrary complex scalar multiplication. -/
theorem ofOperator_smul (c : ℂ) (T : H →L[ℂ] H)
    (hT : ProbabilisticTheory.IsTraceClass T) :
    (c • ofOperator H T hT : TraceClass H).1 = c • T := rfl

#print axioms ProbabilisticTheory.TraceClass.smul_operator
#print axioms ProbabilisticTheory.TraceClass.ofOperator_smul

end ProbabilisticTheory.TraceClass
