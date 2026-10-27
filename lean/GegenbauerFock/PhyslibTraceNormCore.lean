import GegenbauerFock.PhyslibTraceClassSubtype

/-!
# V007: foundational trace-norm axioms toward the full Physlib Banach type

The source-compatible trace-class operator subtype was already
kernel-checked. Here we port two elementary *general* trace-class
norm identities from upstream PhyslibAlpha (Tom Ole Diem, Apache-2.0):
nonnegativity of the genuine CFC trace norm, and membership/norm of
the zero endomorphism. These are necessary, but NOT SUFFICIENT, for a
NormedAddCommGroup or Banach-space construction; additive closure,
triangle inequality, and trace-norm completeness remain separate.

No finite-dimensionality or additional axioms are assumed.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The zero operator is trace-class in any complete complex Hilbert
space, with no finite-dimensionality assumption. -/
theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  exact ⟨w, b, by simp [CFC.abs_zero]⟩

/-- The actual CFC trace norm is nonnegative for EVERY trace-class
endomorphism, not merely for the positive ultraspherical Gram. -/
theorem traceNorm_nonneg (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    0 ≤ traceNorm T hT := by
  unfold traceNorm
  apply tsum_nonneg
  intro i
  exact ((ContinuousLinearMap.nonneg_iff_isPositive).1
    (CFC.abs_nonneg T)).re_inner_nonneg_right _

/-- The trace norm of the zero bounded operator is exactly zero. -/
theorem traceNorm_zero :
    traceNorm (0 : H →L[ℂ] H) isTraceClass_zero = 0 := by
  unfold traceNorm
  simp only [CFC.abs_zero, ContinuousLinearMap.zero_apply,
    inner_zero_right, Complex.zero_re, tsum_zero]

#print axioms ProbabilisticTheory.isTraceClass_zero
#print axioms ProbabilisticTheory.traceNorm_nonneg
#print axioms ProbabilisticTheory.traceNorm_zero

namespace TraceClass

/-- The operator-subtype trace-norm function is nonnegative on
every actual trace-class element. -/
theorem traceNorm_nonneg (T : TraceClass H) :
    0 ≤ traceNorm H T :=
  ProbabilisticTheory.traceNorm_nonneg T.1 T.2

#print axioms ProbabilisticTheory.TraceClass.traceNorm_nonneg

end TraceClass
end ProbabilisticTheory
