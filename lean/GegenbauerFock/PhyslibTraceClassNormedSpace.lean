import GegenbauerFock.PhyslibTraceClassNormedGroup

/-!
# V007 — complex normed-space structure of the CFC trace class

Once the additive S₁ group and the genuine trace norm have been
certified, the pre-existing exact scalar action and absolute
homogeneity give the full complex module and normed-space instances.

This module does NOT assert completeness, which requires the
separate trace-norm lower-semicontinuity and series-limit argument.
It is an independent candidate pending exact-SHA Lean CI.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual scalar action on CFC trace-class operators is
a module action over ℂ; addition is the general S₁ addition. -/
noncomputable instance instGenuineComplexModule : Module ℂ (TraceClass H) where
  smul_add := smul_add_element
  add_smul := add_smul_element
  zero_smul := zero_smul_element
  smul_zero := smul_zero_element

/-- Complex normed-space structure for source-compatible Physlib
S₁, with norm exactly its genuine CFC absolute-value trace norm. -/
noncomputable instance instGenuineComplexNormedSpace :
    NormedSpace ℂ (TraceClass H) where
  norm_smul_le c T := by
    rw [norm_eq_genuineTraceNorm, norm_eq_genuineTraceNorm]
    exact le_of_eq (traceNorm_smul_general c T)

#print axioms ProbabilisticTheory.TraceClass.traceNorm_smul_general

end ProbabilisticTheory.TraceClass
